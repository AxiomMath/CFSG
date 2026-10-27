module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CT2
import CFSG.Certificates.Kernel.A6CK.Facts
import CFSG.Certificates.Kernel.A6CK.Sound
public import Certificates.Kernel.A6CK.Checks

public section

namespace CFSG.KD.A6CK

open CFSG.KC.A6CK Certificates.A6C CFSG.OddStandard.SmallF3.Omega

set_option maxRecDepth 100000

theorem ch442277_bind_G : List.map decM G = (gens6 ()).toList := by decide +kernel
theorem ch442277_bind_EA : List.map decM EA = (eaM6 ()).toList := by decide +kernel
theorem ch442277_bind_ET : List.map decM ET = (etM6 ()).toList := by decide +kernel
theorem ch442277_bind_a0 : decM a0 = a0M6 () := by decide +kernel
theorem ch442277_bind_g0 : decM g0 = g0M6 () := by decide +kernel
theorem ch442277_bind_n0 : decM n0 = nM6 () := by decide +kernel
theorem ch442277_bind_r0 : decM r0 = refl0M6 () := by decide +kernel

theorem a6ck_facts : A6CKFacts := by
  intro Γ _ m hΓ
  obtain ⟨rA, rCA, rT, rCT, rF, h61, h62, h63, h64, hK1, hK2⟩ :=
    a6ck_sound (G := G) (GT := GT) (EA := EA) (ET := ET) (a0 := a0) (g0 := g0) (n0 := n0)
      (tau := tau) (r0 := r0) (AE := A.E) (CAE := CA.E) (TE := T.E) (CTE := CT.E) (FE := F.E)
      (K0 := K0) (AC := A.C) (CAC := CA.C) (TC := T.C) (CTC := CT.C) (FC := F.C) (KA := KA)
      ch442277_bind_G ch442277_bind_EA ch442277_bind_ET ch442277_bind_a0 ch442277_bind_g0
      ch442277_bind_n0 ch442277_bind_r0 ch442277_const ch442277_gens ch442277_ea ch442277_et
      ch442277_A ch442277_Ad ch442277_CA ch442277_CAd ch442277_T ch442277_Td ch442277_CT
      ch442277_CTd ch442277_F ch442277_Fd ch442277_k0 ch442277_pairs
  exact a6c_facts_of_parts m hΓ h61 h62 h63 h64 hK1 hK2

end CFSG.KD.A6CK

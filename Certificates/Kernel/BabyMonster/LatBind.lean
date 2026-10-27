module

public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check10
public import Certificates.Kernel.BabyMonster.TBind
public import Certificates.Data.Kernel.BabyMonster.LatText
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check0
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check1
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check2
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check3
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check4
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check5
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check6
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check7
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check8
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Check9

public section

namespace CertificateChecks.KernelBM.Lat

open CFSG.KC.YModel CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KD.LatBind

theorem text_eq : CFSG.Monster.B.LatText.text = String.ofList (charsOf CFSG.KD.LatBind.CH) := by
  simp only [CFSG.Monster.B.LatText.text, C0.eq, C1.eq, C2.eq, C3.eq, C4.eq, C5.eq, C6.eq, C7.eq,
    C8.eq, C9.eq, C10.eq, ← String.ofList_append, ← CertificateChecks.KernelBM.charsOf_append,
    CFSG.KD.LatBind.CH, CFSG.KD.TBind.appP_eq, List.append_assoc]

theorem basisRows_of_text : ∀ i j : Nat, i < 4371 → j < 4371 →
    ((basisRowsOf CFSG.Monster.B.LatText.text)[i]!.get! j).toNat =
      if j < i then 0 else recOf CFSG.KC.BM.Dyadic.Bs i / 2 ^ (16 * (j - i)) % 65536 := by
  have hr : ∀ s < 69, rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (64 * s)
      (Nat.min 64 (4371 - 64 * s)) = true := by
    forall_lt_consts CFSG.KD.LatBind.r 69
  rw [text_eq]
  exact basisRowsOf_eq CFSG.KD.LatBind.len CFSG.KD.LatBind.diag hr CFSG.KD.LatBind.nz
    CFSG.KD.LatBind.last

end CertificateChecks.KernelBM.Lat

end

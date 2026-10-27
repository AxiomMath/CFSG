module

public import Certificates.Data.M23Asl
import Certificates.Kernel.M23Asl.Checks
import CFSG.Certificates.Kernel.M23AslSound

public section

namespace Certificates

open CFSG.KC.LQT CFSG.KC.M23Asl CFSG.KD.M23Asl M23Asl

theorem certificate7187 : M23Asl.check = true := by
  have eYa : yaGens.map P.code = gYa := by decide +kernel
  have eYb : ybGens.map P.code = gYb := by decide +kernel
  have eAa : aaGens.map P.code = gAa := by decide +kernel
  have eAb : abGens.map P.code = gAb := by decide +kernel
  have eSa : aslA.map P.code = gSa := by decide +kernel
  have eSb : aslB.map P.code = gSb := by decide +kernel
  have eXb : P.code (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW
      [CFSG.Sporadic.Schreier.m23PermA, CFSG.Sporadic.Schreier.m23PermB] wb) = cXb := by
    decide +kernel
  have hA := yxK_sound (by decide) yaGens aaGens _ eYa eAa eXb ya
  have hB := yK_sound (by decide) ybGens abGens eYb eAb yb
  have hDa := diagExt_sound (by decide) (by decide) aaGens aslA eAa eSa da
  have hDb := diagExt_sound (by decide) (by decide) abGens aslB eAb eSb db
  have hT : (sgPerms.map tabP == CFSG.Quasithin.H.MathieuLat.m23STabs) = true := by
    rw [eq_of_beq tabs, eq_of_beq stabs]
    exact beq_self_eq_true _
  rw [M23Asl.check]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, hA.2.1⟩, beq_iff_eq.2 hA.2.2.1⟩, hB.1⟩, beq_iff_eq.2 hB.2.1⟩,
    by rw [hA.1]; rfl⟩, hA.2.2.2⟩, hB.2.2⟩, hDa⟩, hDb⟩

end Certificates

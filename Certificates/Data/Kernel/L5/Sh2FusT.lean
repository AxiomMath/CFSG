module

public import Certificates.Data.Kernel.L5.F5Code
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.L5.Sh2FusT "Certificates/Data/Kernel/L5/data/sh2fus.json.gz" 9834
  9593564629663545965 (embT : List (Nat × Nat)) (f5C : List (Nat × Nat))

namespace CFSG.KD.L5

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.L5.Fus

@[expose] def lookT : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | q :: T, c => if q.1 = c then q.2 else lookT T c

@[expose] noncomputable def eI (c : Nat) : Idx 256 := ⟨⟨lookT Sh2FusT.embT c % 256, Nat.mod_lt _ (by decide)⟩⟩

@[expose] noncomputable def embL (t : ↥T5) : Idx 256 := eI (codeP t.1)

end CFSG.KD.L5

end

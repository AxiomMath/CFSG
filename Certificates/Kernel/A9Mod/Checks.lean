module

public import Certificates.Data.Kernel.A9Mod.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KD.A9Mod "Certificates/Kernel/A9Mod/a9mod.json.gz" 59496 4810992274790683796
  (spin1a : CFSG.KC.A9Mod.SpinRec) (recs1a : List CFSG.KC.A9Mod.S1Rec)
  (node1a : CFSG.KC.A9Mod.NodeRec) (spin1b : CFSG.KC.A9Mod.SpinRec)
  (recs1b : List CFSG.KC.A9Mod.S1Rec) (node2a : CFSG.KC.A9Mod.NodeRec)
  (node2b : CFSG.KC.A9Mod.NodeRec) (node2c : CFSG.KC.A9Mod.NodeRec)

public section

namespace CFSG.KD.A9Mod

open CFSG.KC.A9Mod

theorem ch687010s1a : s1OK N1Q spin1a recs1a (repsOf [node1a]) = true := by decide +kernel

theorem ch687010s1b : s1OK N2Q spin1b recs1b (repsOf [node2a, node2b, node2c]) = true := by
  decide +kernel

theorem ch687010n1a : nodeOK N1Q node1a = true := by decide +kernel

theorem ch687010n2a : nodeOK N2Q node2a = true := by decide +kernel

theorem ch687010n2b : nodeOK N2Q node2b = true := by decide +kernel

theorem ch687010n2c : nodeOK N2Q node2c = true := by decide +kernel

theorem ch687010s1a_neg : s1OK N1Q spin1a (List.drop 1 recs1a) (repsOf [node1a]) = false := by
  decide +kernel

theorem ch687010n1a_neg : nodeOK N1Q (node1a.1, (node1a.2.1, List.drop 1 node1a.2.2)) = false := by
  decide +kernel

theorem ch687010n1a_negw :
    nodeOK N1Q (node1a.1, (node1a.2.1, node1a.2.2.map fun s => (s.1, (s.2.1, [])))) = false := by
  decide +kernel

end CFSG.KD.A9Mod

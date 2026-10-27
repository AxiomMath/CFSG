module

public import Certificates.Kernel.AE6ModC.Checks
public import Certificates.Kernel.AE6Core.Final

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6ModC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.KC.HeGlueK CFSG.KC.AE6F CFSG.KC.AE6Core CFSG.KC.AE6ModC CFSG.KS.SporSch.MOC
  Certificates.AE6Model Certificates.S7Twin CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Co2.Native
open CFSG.KC.Child3 (tabP)
open CertificateChecks.KernelAE6F (RG WL gensRG allTables_wQ hsz tabP_eq_tabN)
open CertificateChecks.KernelAE6Core (chainPL evalCodes_eq)

theorem ppTLP : ∀ L ∈ trPL 360 9 KernelAE6Core.PL.LR KernelAE6Core.PL.TR 4, ∀ t ∈ L, PP 360 9 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTRP L hL) t ht)

theorem allTables_plQ : allTables (plQ ()) = PLL.map (tabN 360 9) := by
  have hL : levelTables (plQ ()) =
      (trPL 360 9 KernelAE6Core.PL.LR KernelAE6Core.PL.TR 4).map (List.map (tabP 360 9)) :=
    levelTables_eq chainPL (by decide) (by decide)
  have h := filterProducts_tabP (n := 360) (w := 9) (f := allTrue) (fk := fun _ => true)
    (fun _ _ => rfl) _ ppTLP (pidn 360 9) [] (PP.id hsz)
  rw [List.map_nil] at h
  rw [allTables, hL, idT_tabP hsz, h]
  unfold PLL
  exact List.map_congr_left fun x hx => tabP_eq_tabN (PP_pfilterProducts hsz _ ppTLP _ []
    (PP.id hsz) (fun _ h => absurd h List.not_mem_nil) x hx)

theorem getD_map_aeWord (L : List (List Nat)) (i : Nat) :
    (L.map (aeWord (curtisPerms ()))).getD i 1 = aeWord (curtisPerms ()) (L.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

theorem c3Perms_eq : c3Perms () = (cwN C3W.chars).map (aeWord (curtisPerms ())) := by
  have hw : (c3Words ()).map (List.map fun z => z.natAbs - 1) = cwN C3W.chars := by
    rw [C3W.eq, parseWords_ofList _ kToks3]
    rfl
  unfold c3Perms
  simp only
  rw [← hw, List.map_map]
  exact List.map_congr_left fun w _ => evalCodes_eq w

theorem c1Perms_eq : c1Perms () = (cwN C1W.chars).map (aeWord (curtisPerms ())) := by
  have hw : (c1Words ()).map (List.map fun z => z.natAbs - 1) = cwN C1W.chars := by
    rw [C1W.eq, parseWords_ofList _ kToks1]
    rfl
  unfold c1Perms
  simp only
  rw [← hw, List.map_map]
  exact List.map_congr_left fun w _ => evalCodes_eq w

theorem c1iPerms_eq : c1iPerms () = (cwN C1IW.chars).map (aeWord (curtisPerms ())) := by
  have hw : (c1iWords ()).map (List.map fun z => z.natAbs - 1) = cwN C1IW.chars := by
    rw [C1IW.eq, parseWords_ofList _ kToks1i]
    rfl
  unfold c1iPerms
  simp only
  rw [← hw, List.map_map]
  exact List.map_congr_left fun w _ => evalCodes_eq w

theorem ae6C3_eq : ae6C3 () = c3N RG WL PLL (cwN C3W.chars) := by
  unfold ae6C3 c3N z0
  simp only [allTables_wQ, allTables_plQ, c3Perms_eq, List.map_map, List.all_map, List.any_map,
    Function.comp_def, memT_tabN, toTable_mul (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32), toTable_aeWord gensRG.get, invT_tabN' dims,
    compT_tabN' dims, tblEq_tabN' dims, CFSG.KC.AE6ModC.cjN]

theorem ae6C1_eq : ae6C1 () = c1N RG PLL (cwN C1W.chars) := by
  unfold ae6C1 c1N z0
  simp only [allTables_plQ, c1Perms_eq, List.length_map, getD_map_aeWord, memT_tabN,
    toTable_mul (by norm_num : (360 : Nat) < 2 ^ 32), toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_aeWord gensRG.get, gensRG.get, invT_tabN' dims, compT_tabN' dims, CFSG.KC.AE6ModC.cjN]

theorem ae6C1i_eq : ae6C1i () = c1iN RG PLL (cwN C1IW.chars) := by
  unfold ae6C1i c1iN z0
  simp only [allTables_plQ, c1iPerms_eq, List.length_map, getD_map_aeWord, memT_tabN,
    toTable_mul (by norm_num : (360 : Nat) < 2 ^ 32), toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_aeWord gensRG.get, gensRG.get, invT_tabN' dims, compT_tabN' dims, CFSG.KC.AE6ModC.cjN]

theorem ae6C3_k : ae6C3 () = true := ae6C3_eq.trans kC3

theorem ae6C1_k : ae6C1 () = true := ae6C1_eq.trans kC1

theorem ae6C1i_k : ae6C1i () = true := ae6C1i_eq.trans kC1i

end CertificateChecks.KernelAE6ModC

end

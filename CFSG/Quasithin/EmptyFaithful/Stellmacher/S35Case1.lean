module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ctx
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpFinal
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LtA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10F
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10G
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8bMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56bD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cGD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7A4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7K
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7W
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7P
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7D2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7E
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem caseI_false (hS : Sit H M S) (hI : CaseI H M) : False := by
  have hC := ctx_of_caseI hS hI
  have hclaimR := At.claimR hC
  have h9 := At.claim9 hC
  have h16a := At.claim16a hC
  have h15c := At.claim15c hC
  have hsec := B5.wb_isSec hS h15c
  have hT := Lt.claimT hS hI
  have h8a := E8.claim8a hS hC.orthZ
  have h6b := C56.claim6b hS hI
  have h6a := C56.claim6a hS hI
  have h5b := C56.claim5b hS hI
  have h7 := G7.D.claim7s_of_pm hS hC.orthZ h15c (G7.claim16d hS hI hC.orthZ hC.hR)
      (G7.pm hS hI hC.orthZ hC.hR h5b h6b G7.abstractPlaneLemma G7.lem81 G7.K.kernelStruct
          G7.wmoduleExists)
  have h8b := E8.claim8b hS hI hC.orthZ hT h7 h8a h6b hsec
  have hLP := Lp.claimLP hS hI hC.orthZ hC.hR hclaimR
  have h10 := E10.claim10 hS hclaimR hLP h9 h8a h7 hT h16a hsec
  have h11 := E10.claim11 hS hI h10 h16a
  have h13 := B5.claim13_core hC h10 h11 h15c hclaimR h6a h6b
  have hb7 : 7 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := hS.glob.odd
    have := hS.b5
    have h13' := h13
    unfold Claim13 at h13'
    omega
  have h14 := E14.claim14 hS hI hb7 hclaimR h8b h16a
  have h15a := E14.claim15a h14 h8b h9 h16a
  exact Fn.caseI_false hS hI hC.orthZ hC.hR h10 h16a h8a h14 h15a h15c hclaimR

end S35

end F53.Stellmacher

end CFSG.Quasithin

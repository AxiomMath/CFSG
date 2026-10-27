module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Final2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sd2A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sd2T
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C3Claim3a
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C3Claim3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2TT
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Nbar
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Cent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35S6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35S6C5b
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K6b
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K8aMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T3Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2C
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35A10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35A10SMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L81A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L81B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K8bMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L192Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L192C
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TBaMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB23
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB4Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21NbarDich
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Sub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem caseII_false_of_sit (hS : Sit H M S) (hII : CaseII H M) : False := by
  have h3a := C3.claim3a_of hS
  have h3 := C3.claim3_of hS hII h3a
  have hLP := Lp2.claimLP_II hS hII
  have hTT := Lp2.claimTT_II hS hII
  have hNb := Lp2.nbarThat_II hS hII hLP
  have h16 := L16.claim16a_II hS
  have hRC := L16.rCent_II hS
  have hZb := Col.zvBlock_II hS
  have hZinf := Col.zvInf_II hS
  have hRk := Col.rkZvEq_II hS
  have hTF := Col.thatFacts_II hS
  have hS6 := S6.claimS6 hS
  have h6a := S6.claim6a hS
  have h5b := S6.claim5b_II hS
  have h6b := K6b.claim6b hS hII h6a
  have hT := Sd2.claimT_II hS hII
  have hNT := Sd2.noTrivialAct hS
  have hWb7 := Sd2.wbSec7 hS
  have hcrit := Sd2.pdCrit hS
  have h8a := K8a.claim8a_II hS hRk
  have h9 := N9.claim9T hS hII h6b hNb h3a
  have hs1 := T1.step1 hS hII hNb hRC hRk
  have h21 := T21.step21 hS hII
  have hs2 := T2L.step2L hS hII
  have hs3 := T3.step3 hS hII h21 hS6
  have hs2C := T2C.step2C hS
  have h7s := II.lemma7s_of_steps hS h3 hTT hs1 hs2 hs3
  have hA := A10.claim10A hS
  have hB := A10.claim10B hS h8a hT
  have hC := A10.claim10C hS h9 h8a hT hNT h7s
  have hSym := A10S.claim10Sym hS h3a hTT h9 h8a h16 h7s
  have h81 := L81.lem81II hS hII h5b h6b
  have h191 := L81.lem191II hS hII h6b
  have h7 := K8b.claim7s_II hS (II.noTransvII_of_lem h81 h191)
  have h8b : 7 ≤ bMin H M → Claim8b H M := fun hb7 =>
    K8b.claim8b_II hS hb7 hT h7 h8a hNT hWb7
  have h192 : 7 ≤ bMin H M → II.Lem192 H M := fun hb7 =>
    L192.lem192_II hS hb7 h16 hTT h9 h3 (h8b hb7) hSym
  have h8C : 7 ≤ bMin H M → II.Claim8aC H M := fun hb7 =>
    L192.claim8aC_II hS hRk h8a (h192 hb7) h16 hSym
  have hBa := II.thmBa h3a
  have hNd := T21.nbarDich hS hNb hTF
  have hSub := T21.suborbitDich hS
  have hc23 := TB23.thmBcase23 hS hII hTF hNb
  have hc4 := TB4.thmBcase4_II hS hII hZb hNb hTF hS6
  exact II.caseII_false_of_nodes hS hcrit hLP hTT h16 h3 h3a hRC hZb hZinf hA hB hC hSym h6b hs1
    hs3 h192 h8C (fun _ => hs2C) hBa hNd hSub hc23 hc4

end S35

end F53.Stellmacher

end CFSG.Quasithin

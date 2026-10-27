module

public import CFSG.Quasithin.H13.NQCatT513Hall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem cycOddPerm_m22Grp : CycOddPerm ↥Mgrp fun _ => False := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have hUc : Nat.card ↥Ugrp = 128 :=
    card_of_isSylowTwoOf_top hU (a := 7) (m := 3465) (cert.card_m (rawIsEnc 22) hcl hsz)
      (by decide)
  refine cycOddPerm_of_overgroups hU fun Z hZ m hm => ?_
  obtain ⟨j, hj, hLM, hZL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck Z hZ
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  rw [hZL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj, hUc] at hm
  have hs : cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  rw [hs] at hm
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hm <;> omega

theorem cycOddPerm_m22 :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .M22) fun _ => False :=
  cycOddPerm_m22Grp.of_equiv (MulEquiv.subgroupCongr mGens_closure)

end CFSG.Quasithin.H13.NQCat.T513P

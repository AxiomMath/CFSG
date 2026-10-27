
module


public import Certificates.Certificate7210

public section

namespace CFSG.Quasithin.KGC31.M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native _root_.Certificates

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native _root_.Certificates

theorem c_ord5 :
    ordTest 23 5 x5T = true := by
  obtain ⟨h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ord7 :
    ordTest 23 7 x7T = true := by
  obtain ⟨-, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ord11 :
    ordTest 23 11 x11T = true := by
  obtain ⟨-, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ord23 :
    ordTest 23 23 x23T = true := by
  obtain ⟨-, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_orb5 :
    orbCheck 23 5 invs (powTabs 23 x5T 5) cands5 = true := by
  obtain ⟨-, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_orb7 :
    orbCheck 23 7 invs (powTabs 23 x7T 7) cands7 = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_act11 :
    actCheck 23 11 invs (powTabs 23 x11T 11) = true := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_act23 :
    actCheck 23 23 invs (powTabs 23 x23T 23) = true := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_candInv :
    ((List.range 8).all fun k => invOK 23 (candT k) (invT 23 (candT k))) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eb_w :
    ebasisOK 23 wT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eb_duad :
    ebasisOK 23 tT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eb_e8 :
    ebasisOK 23 eT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eb_s :
    ebasisOK 23 sT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_cent_w_count :
    cbT.countP (commAll 23 wT) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_cent_duad_count :
    cbT.countP (commAll 23 tT) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_cent_e8_count :
    cbT.countP (commAll 23 eT) = 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_cent_s_count :
    cbT.countP (commAll 23 sT) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_coset_w :
    cosetOK 23 b0T wT wCosetT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_coset_duad :
    cosetOK 23 b0T tT tCosetT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_coset_e8 :
    cosetOK 23 b0T eT eCosetT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ccount_w :
    cosetCount 23 cbT wCosetT (normAll 23 wT) = 40320 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ccount_duad :
    cosetCount 23 cbT tCosetT (fun g => normAll 23 tT g && fixesAll g triT) = 960 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_ccount_e8 :
    cosetCount 23 cbT eCosetT (normAll 23 eT) = 1344 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_wChain_check :
    wChain.check = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_wChain_order :
    wChain.orderCertificate = 40320 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_tChain_check :
    tChain.check = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_tChain_order :
    tChain.orderCertificate = 960 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eChain_check :
    eChain.check = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_eChain_order :
    eChain.orderCertificate = 1344 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h,
    -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_masks_w :
    (wGen.zip wMasks).all (fun p => masksOK 23 wT (toTable p.1) p.2) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_masks_duad :
    (tGen.zip tMasks).all (fun p => masksOK 23 tT (toTable p.1) p.2) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_masks_e8 :
    (eGen.zip eMasks).all (fun p => masksOK 23 eT (toTable p.1) p.2) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_tGen_fix :
    (tGen.all fun g => fixesAll (toTable g) triT) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_fix_w :
    fixSetIs 23 wT hexH = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_fix_duad :
    fixSetIs 23 tT triT = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_kerH :
    countProducts 23 (fun g => fixesAll g hexH) (levelTables wChain) (idT 23) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, h, -⟩ :=
    Certificates.certificate7210
  exact h

theorem c_s_in_w :
    (sT.length == sInW.length && (sT.zip sInW).all fun p => tblEq 23 p.1 (maskProd 23 wT p.2)) =
      true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, h⟩ :=
    Certificates.certificate7210
  exact h
end CFSG.Quasithin.KGC31.M23

end

module

public import Certificates.Certificate7216
public import Certificates.Certificate7217

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Certificates _root_.Certificates

theorem a_ord5 :
    ordTest 24 5 x5T = true := by
  obtain ⟨h, -⟩ := Certificates.certificate7216
  exact h

theorem a_ord7 :
    ordTest 24 7 x7T = true := by
  obtain ⟨-, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_ord11 :
    ordTest 24 11 x11T = true := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_ord23 :
    ordTest 24 23 x23T = true := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_orb5 :
    orbCheck 24 5 invs [x5T] cands5 = true := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_orb7 :
    orbCheck 24 7 invs [x7T] cands7 = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_act11 :
    actCheck 24 11 invs [x11T] = true := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_act23 :
    actCheck 24 23 invs [x23T] = true := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_candInv :
    ((List.range 26).all fun k => invOK 24 (candT k) (invT 24 (candT k))) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_frameInv :
    (frameConjT.all fun c => invOK 24 c (invT 24 c)) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_frame0 :
    frameCheck 24 7 x7T (conjAll (candT 12) u5T) (frameVs 12) (frameCands fr0W) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_frame1 :
    frameCheck 24 7 x7T (conjAll (candT 17) u5T) (frameVs 17) (frameCands fr1W) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := Certificates.certificate7216
  exact h

theorem a_frame2 :
    frameCheck 24 7 x7T (conjAll (candT 18) u5T) (frameVs 18) (frameCands fr2W) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := Certificates.certificate7216
  exact h

theorem c_g1 :
    ((tblEq 24 b0T (toTable (m24InvReps.getD 1 1))) &&
      (tblEq 24 b1T (toTable (m24InvReps.getD 0 1))) && (ebasisOK 24 oT) && (ebasisOK 24 sT) &&
      (ebasisOK 24 s16T) && (ebasisOK 24 s32T) && (ebasisOK 24 r2T) && (ebasisOK 24 u4T) &&
      (ebasisOK 24 u5T) && (ebasisOK 24 u6T) && (ebasisOK 24 tT) && (ebasisOK 24 etT)) = true := by
  obtain ⟨h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g2 :
    ((cb0T.countP (commAll 24 oT) == 16) && (cb0T.countP (commAll 24 sT) == 64) &&
      (cb0T.countP (commAll 24 s16T) == 64) && (cb0T.countP (commAll 24 s32T) == 64) &&
      (cb0T.countP (commAll 24 r2T) == 16) && (cb0T.countP (commAll 24 u4T) == 16) &&
      (cb0T.countP (commAll 24 u5T) == 128) && (cb0T.countP (commAll 24 tT) == 64) &&
      (cb1T.countP (commAll 24 u6T) == 64)) = true := by
  obtain ⟨-, h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g3 :
    ((sT.all (commAll 24 s16T)) && (sT.all (commAll 24 s32T)) && (invOK 24 d4T (invT 24 d4T)) &&
      ((conjAll d4T r2T).all (commAll 24 u4T)) && (invOK 24 d6T (invT 24 d6T)) &&
      ((conjAll d6T tT).all (commAll 24 u6T)) &&
      (qGen.all fun g => commAll 24 u5T (toTable g))) = true := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g4 :
    (moChain.check && (moChain.orderCertificate == 322560) && nsChain.check &&
      (nsChain.orderCertificate == 138240) && lsChain.check &&
      (lsChain.orderCertificate == 69120) && qChain.check && (qChain.orderCertificate == 128) &&
      nqChain.check && (nqChain.orderCertificate == 21504) && lqChain.check &&
      (lqChain.orderCertificate == 10752) && ntChain.check && (ntChain.orderCertificate == 64512) &&
      kqChain.check && (kqChain.orderCertificate == 21504)) = true := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g5 :
    (((moGen.zip moMasks).all (fun p => masksOK 24 oT (toTable p.1) p.2)) &&
      ((nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2)) &&
      (masksOK 24 sT y5T y5Masks) && ((njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2)) &&
      ((nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2)) &&
      (masksOK 24 u5T y7T y7Masks) && ((mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2)) &&
      ((ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2)) &&
      (masksOK 24 tT qtT qtMasks) && ((kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2)) &&
      ((cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2)) &&
      (ordTest 24 5 y5T) && (ordTest 24 7 y7T)) = true := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g6 :
    ((sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) &&
      (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) && (etT.all (commAll 24 u5T)) &&
      (countProducts 24 (commAll 24 u5T) (levelTables lqChain) (idT 24) == 64) &&
      (blocksOK tets y5T) && (njT.all (blocksOK tets)) && (sT.all (fixesBlocks tets)) &&
      (countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) == 192)) = true := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate7217
  exact h

theorem c_g7 :
    (!(inSpan 24 tT qtT) && (inSpan 24 tT (compT 24 qtT qtT)) && (invOK 24 qtT (invT 24 qtT)) &&
      (kqT.all fun k => invOK 24 k (invT 24 k) &&
        inSpan 24 tT (compT 24 (conjTab 24 k (invT 24 k) qtT) (invT 24 qtT))) &&
      (cosetOK 24 b0T r2T r2CosetT) &&
      (cosetCount 24 cb0T r2CosetT (normAll 24 r2T) == 21504)) = true := by
  obtain ⟨-, -, -, -, -, -, h⟩ := Certificates.certificate7217
  exact h

theorem c_b0 :
    tblEq 24 b0T (toTable (m24InvReps.getD 1 1)) = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_b1 :
    tblEq 24 b1T (toTable (m24InvReps.getD 0 1)) = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_eb_o :
    ebasisOK 24 oT = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_eb_s :
    ebasisOK 24 sT = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_s16 :
    ebasisOK 24 s16T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_s32 :
    ebasisOK 24 s32T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_r2 :
    ebasisOK 24 r2T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_u4 :
    ebasisOK 24 u4T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_u5 :
    ebasisOK 24 u5T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_u6 :
    ebasisOK 24 u6T = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_t :
    ebasisOK 24 tT = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_eb_et :
    ebasisOK 24 etT = true := by
  have h₀ := c_g1
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_cent_o :
    cb0T.countP (commAll 24 oT) = 16 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_cent_s :
    cb0T.countP (commAll 24 sT) = 64 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_cent_s16 :
    cb0T.countP (commAll 24 s16T) = 64 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_cent_s32 :
    cb0T.countP (commAll 24 s32T) = 64 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_cent_r2 :
    cb0T.countP (commAll 24 r2T) = 16 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_cent_u4 :
    cb0T.countP (commAll 24 u4T) = 16 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_cent_u5 :
    cb0T.countP (commAll 24 u5T) = 128 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_cent_t :
    cb0T.countP (commAll 24 tT) = 64 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_cent_u6 :
    cb1T.countP (commAll 24 u6T) = 64 := by
  have h₀ := c_g2
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_comm_s16 :
    sT.all (commAll 24 s16T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_comm_s32 :
    sT.all (commAll 24 s32T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_d4_inv :
    invOK 24 d4T (invT 24 d4T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_d4_comm :
    (conjAll d4T r2T).all (commAll 24 u4T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_d6_inv :
    invOK 24 d6T (invT 24 d6T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_d6_comm :
    (conjAll d6T tT).all (commAll 24 u6T) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_q_comm :
    (qGen.all fun g => commAll 24 u5T (toTable g)) = true := by
  have h₀ := c_g3
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_mo_check :
    moChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_mo_order :
    moChain.orderCertificate = 322560 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_ns_check :
    nsChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_ns_order :
    nsChain.orderCertificate = 138240 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_ls_check :
    lsChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_ls_order :
    lsChain.orderCertificate = 69120 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_q_check :
    qChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_q_order :
    qChain.orderCertificate = 128 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_nq_check :
    nqChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_nq_order :
    nqChain.orderCertificate = 21504 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_lq_check :
    lqChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_lq_order :
    lqChain.orderCertificate = 10752 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_nt_check :
    ntChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_nt_order :
    ntChain.orderCertificate = 64512 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_kq_check :
    kqChain.check = true := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_kq_order :
    kqChain.orderCertificate = 21504 := by
  have h₀ := c_g4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_masks_mo :
    ((moGen.zip moMasks).all (fun p => masksOK 24 oT (toTable p.1) p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_masks_ns :
    ((nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_masks_y5 :
    masksOK 24 sT y5T y5Masks = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_masks_nj :
    ((njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_nq :
    ((nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_y7 :
    masksOK 24 u5T y7T y7Masks = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_mj :
    ((mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_nt :
    ((ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_qt :
    masksOK 24 tT qtT qtMasks = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_kq :
    ((kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_masks_cb0 :
    ((cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2)) = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_ord_y5 :
    ordTest 24 5 y5T = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_ord_y7 :
    ordTest 24 7 y7T = true := by
  have h₀ := c_g5
  simp only [Bool.and_eq_true, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_sift_s :
    (sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_sift_et :
    (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_et_comm :
    etT.all (commAll 24 u5T) = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_lq_cent :
    countProducts 24 (commAll 24 u5T) (levelTables lqChain) (idT 24) = 64 := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_blocks_y5 :
    blocksOK tets y5T = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_blocks_nj :
    njT.all (blocksOK tets) = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_fix_s :
    sT.all (fixesBlocks tets) = true := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, h, -⟩ := h₀
  exact h

theorem c_ker_ls :
    countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) = 192 := by
  have h₀ := c_g6
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h₀
  obtain ⟨-, -, -, -, -, -, -, h⟩ := h₀
  exact h

theorem c_qt_notin :
    inSpan 24 tT qtT = false := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨h, -⟩ := h₀
  exact h

theorem c_qt_sq :
    inSpan 24 tT (compT 24 qtT qtT) = true := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨-, h, -⟩ := h₀
  exact h

theorem c_qt_inv :
    invOK 24 qtT (invT 24 qtT) = true := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨-, -, h, -⟩ := h₀
  exact h

theorem c_kq_comm :
    (kqT.all fun k => invOK 24 k (invT 24 k) &&
      inSpan 24 tT (compT 24 (conjTab 24 k (invT 24 k) qtT) (invT 24 qtT))) = true := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨-, -, -, h, -⟩ := h₀
  exact h

theorem c_coset_r2 :
    cosetOK 24 b0T r2T r2CosetT = true := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨-, -, -, -, h, -⟩ := h₀
  exact h

theorem c_ccount_r2 :
    cosetCount 24 cb0T r2CosetT (normAll 24 r2T) = 21504 := by
  have h₀ := c_g7
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h₀
  obtain ⟨-, -, -, -, -, h⟩ := h₀
  exact h

end CFSG.Quasithin.KGC31.M24

end

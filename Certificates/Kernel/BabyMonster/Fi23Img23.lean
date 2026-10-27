module

public import Certificates.Kernel.BabyMonster.Fi23InB
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.RankLin
public import CFSG.Certificates.Kernel.BabyMonster.R0Rank.All
public import CFSG.Certificates.Kernel.BabyMonster.R0Rank.Check0

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelBM.Fi23Img23

open CFSG.KC.BM CFSG.KC.BM.Fi23Glue CFSG.Sporadic.GLQ CFSG.Sporadic.Bridge.Fi23GPL.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
  CertificateChecks.KernelBM.Fi23InB

local notation "sm" => stripMat

local notation "Mat" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem phi_img23 {G : Type*} [Group G] (φ : G →* Mat) {U V : G} (hU : φ U = sm Fi23.U)
    (hV : φ V = sm Fi23.V) :
    φ (signedWord U V (imgWords ())[2]! * signedWord U V (imgWords ())[3]!) = sm Fi23R.e23 := by
  have hwU : φ (signedWord U V wU) = sm Fi23.U := by simp [wU, signedWord, letter, hU]
  have hwV : φ (signedWord U V wV) = sm Fi23.V := by simp [wV, signedWord, letter, hV]
  have k0 : φ (signedWord U V g0W) = sm Fi23.g0 := phiW φ hwV Fi23.wf_V [wU] [Fi23.U]
    (.cons ⟨hwU, Fi23.wf_U⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg0 69)
  have k1 : φ (signedWord U V g1W) = sm Fi23.g1 := phiW φ k0 Fi23.wf_g0 [wV] [Fi23.V]
    (.cons ⟨hwV, Fi23.wf_V⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg1 69)
  have k2 : φ (signedWord U V g2W) = sm Fi23.g2 := phiW φ k0 Fi23.wf_g0 [g0W] [Fi23.g0]
    (.cons ⟨k0, Fi23.wf_g0⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg2 69)
  have k3 : φ (signedWord U V g3W) = sm Fi23.g3 := phiW φ k1 Fi23.wf_g1 [g1W] [Fi23.g1]
    (.cons ⟨k1, Fi23.wf_g1⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg3 69)
  have k4 : φ (signedWord U V g4W) = sm Fi23.g4 := phiW φ k2 Fi23.wf_g2 [g0W] [Fi23.g0]
    (.cons ⟨k0, Fi23.wf_g0⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg4 69)
  have k5 : φ (signedWord U V g5W) = sm Fi23.g5 := phiW φ k3 Fi23.wf_g3 [g4W] [Fi23.g4]
    (.cons ⟨k4, Fi23.wf_g4⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg5 69)
  have k6 : φ (signedWord U V g6W) = sm Fi23.g6 := phiW φ k1 Fi23.wf_g1 [g2W] [Fi23.g2]
    (.cons ⟨k2, Fi23.wf_g2⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg6 69)
  have k8 : φ (signedWord U V g8W) = sm Fi23.g8 := phiW φ k5 Fi23.wf_g5 [g5W] [Fi23.g5]
    (.cons ⟨k5, Fi23.wf_g5⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg8 69)
  have k10 : φ (signedWord U V g10W) = sm Fi23.g10 := phiW φ k3 Fi23.wf_g3 [g2W] [Fi23.g2]
    (.cons ⟨k2, Fi23.wf_g2⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg10 69)
  have k11 : φ (signedWord U V g11W) = sm Fi23.g11 := phiW φ k6 Fi23.wf_g6 [g2W] [Fi23.g2]
    (.cons ⟨k2, Fi23.wf_g2⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg11 69)
  have k14 : φ (signedWord U V g14W) = sm Fi23.g14 := phiW φ k2 Fi23.wf_g2 [g2W] [Fi23.g2]
    (.cons ⟨k2, Fi23.wf_g2⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cg14 69)
  have q2 : φ (signedWord U V (pW 2)) = sm Fi23.p2 :=
    phiW φ k11 Fi23.wf_g11 [g10W, g14W, g14W, g1W] [Fi23.g10, Fi23.g14, Fi23.g14, Fi23.g1]
    (.cons ⟨k10, Fi23.wf_g10⟩ (.cons ⟨k14, Fi23.wf_g14⟩ (.cons ⟨k14, Fi23.wf_g14⟩
      (.cons ⟨k1, Fi23.wf_g1⟩ .nil)))) (by bm_strips2 CFSG.KC.BM.Fi23.cp2 69)
  have q3 : φ (signedWord U V (pW 3)) = sm Fi23.p3 := phiW φ k4 Fi23.wf_g4 [g8W] [Fi23.g8]
    (.cons ⟨k8, Fi23.wf_g8⟩ .nil) (by bm_strips2 CFSG.KC.BM.Fi23.cp3 69)
  have qD : φ (signedWord U V dW) = sm Fi23.D :=
    phiW φ hwU Fi23.wf_U [g2W, g8W, g8W, g8W, g3W, wV]
    [Fi23.g2, Fi23.g8, Fi23.g8, Fi23.g8, Fi23.g3, Fi23.V]
    (.cons ⟨k2, Fi23.wf_g2⟩ (.cons ⟨k8, Fi23.wf_g8⟩ (.cons ⟨k8, Fi23.wf_g8⟩
      (.cons ⟨k8, Fi23.wf_g8⟩ (.cons ⟨k3, Fi23.wf_g3⟩ (.cons ⟨hwV, Fi23.wf_V⟩ .nil))))))
    (by bm_strips2 CFSG.KC.BM.Fi23.cD 69)
  have i2 : φ (signedWord U V (imgWords ())[2]!) = sm Fi23.img2 := by
    rw [imgWords_split 2 (by norm_num)]
    exact phi_img φ q2 qD (pW_letters 2 (by norm_num)) Fi23.wf_p2 Fi23.wf_D Fi23.wf_img2
      (by bm_strips2 CFSG.KC.BM.Fi23.cimg2 69)
  have i3 : φ (signedWord U V (imgWords ())[3]!) = sm Fi23.img3 := by
    rw [imgWords_split 3 (by norm_num)]
    exact phi_img φ q3 qD (pW_letters 3 (by norm_num)) Fi23.wf_p3 Fi23.wf_D Fi23.wf_img3
      (by bm_strips2 CFSG.KC.BM.Fi23.cimg3 69)
  exact phi_mul φ i2 i3 Fi23.wf_img2 Fi23.wf_img3 (by bm_strips2 CFSG.KC.BM.Fi23R.ce23 69)

theorem rank_e23 : (sm Fi23R.e23 - 1).rank = 2862 :=
  FiveA.rank_sub_one_of_cert (by norm_num) Fi23R.wf_e23 R0.wf_P R0.wf_Q
    (by bm_stripsx CFSG.KC.BM.R0.rk_ 69) R0.shape R0.ech

open CFSG.Blueprint in
theorem rank_r0_of_seeds :
    ∀ x y : NativeSporadic.B,
      ((x : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
          Mat) = NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1 →
      ((y : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
          Mat) = NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 →
      Matrix.rank ((((signedWord (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2)
            (imgWords ())[2]! *
          signedWord (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2)
            (imgWords ())[3]! : NativeSporadic.B) :
          NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
          Mat) - 1) = 2862 := by
  intro x y hx hy
  let S := NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2
  let φ : Sˣ →* Mat := S.subtype.comp (Units.coeHom S)
  have hx' : φ x = sm Seeds.A1 := by
    change ((x : S) : Mat) = _
    rw [hx]
    exact KernelBM.genA₁_eq_stripMat
  have hy' : φ y = sm Seeds.A2 := by
    change ((y : S) : Mat) = _
    rw [hy]
    exact KernelBM.genA₂_eq_stripMat
  obtain ⟨h1, h2⟩ := regs_phi φ hx' hy'
  generalize runProg (initRegs x y) slp 1 = R₁ at h1 ⊢
  generalize runProg (initRegs x y) slp 2 = R₂ at h2 ⊢
  have e : (((signedWord R₁ R₂ (imgWords ())[2]! * signedWord R₁ R₂ (imgWords ())[3]! : Sˣ) :
      S) : Mat) = sm Fi23R.e23 := phi_img23 φ h1 h2
  rw [e]
  exact rank_e23

end CertificateChecks.KernelBM.Fi23Img23

end

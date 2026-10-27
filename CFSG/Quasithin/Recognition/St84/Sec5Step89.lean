module

public import CFSG.Quasithin.Recognition.St84.Sec5GA
public import CFSG.Quasithin.Recognition.St84.CentralZData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.Quasithin.Background.D14Groups
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S14118

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem subgroupOf_inf_centralizer_normal {L Z : Subgroup G} (hZL : Z ≤ L)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) :
    ((L ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf L).Normal := by
  have hPrice : (Z.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLZ
  have hCLeq : (L ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf L =
      Subgroup.centralizer ((Z.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    ext x
    constructor
    · intro hx
      have hx' := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro ⟨z, hzL⟩ hzZ
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx'.2 z hzZ)
    · intro hx
      refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      have hzL : z ∈ L := hZL hz
      have h := Subgroup.mem_centralizer_iff.mp hx ⟨z, hzL⟩ hz
      exact congrArg Subtype.val h
  rw [hCLeq]
  exact Subgroup.normal_centralizer

private theorem eq_top_of_Q_zero_le_of_normal (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {C : Subgroup ↥(Y.L 0)} [C.Normal]
    (hQC : (Y.Q 0).subgroupOf (Y.L 0) ≤ C)
    (hC : ¬ C ≤ (Y.Q 0).subgroupOf (Y.L 0)) : C = ⊤ := by
  classical
  set QL : Subgroup ↥(Y.L 0) := (Y.Q 0).subgroupOf (Y.L 0) with hQLdef
  have hLnormQ : Y.L 0 ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
    (Y.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hQLnormal : QL.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLnormQ
  haveI : QL.Normal := hQLnormal
  have hN : IsLocL2 Γ G (Y.vert 0) (Y.n 0) (Y.L 0) := Y.hyp.isLocL2_oTwoPrime (Y.vert 0)
  have hqeq : QL = CFSG.pCore 2 ↥(Y.L 0) := by
    rw [hQLdef, ← CFSG.openPCoreOf_subgroupOf 2 (Y.L 0), hN.pCoreOf_eq]
  have h2n : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  have hcardF : 4 ≤ Nat.card (GaloisField 2 (Y.n 0)) := by
    rw [GaloisField.card (p := 2) (n := Y.n 0) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Y.n 0 := Nat.pow_le_pow_right (by norm_num) h2n
  obtain ⟨e⟩ := hN.quot
  haveI hsimplePSL : IsSimpleGroup (PSL(2, GaloisField 2 (Y.n 0))) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  haveI hsimplePcore : IsSimpleGroup (↥(Y.L 0) ⧸ CFSG.pCore 2 ↥(Y.L 0)) :=
    e.isSimpleGroup_congr.mpr hsimplePSL
  haveI hsimpleQ : IsSimpleGroup (↥(Y.L 0) ⧸ QL) :=
    (QuotientGroup.quotientMulEquivOfEq hqeq.symm).isSimpleGroup_congr.mp hsimplePcore
  let π : ↥(Y.L 0) →* (↥(Y.L 0) ⧸ QL) := QuotientGroup.mk' QL
  let M : Subgroup (↥(Y.L 0) ⧸ QL) := C.map π
  have hMnormal : M.Normal :=
    Subgroup.Normal.map (inferInstance : C.Normal) π (QuotientGroup.mk'_surjective QL)
  haveI : M.Normal := hMnormal
  have hMne : M ≠ ⊥ := by
    intro hbot
    apply hC
    intro x hx
    have hxM : π x ∈ M := Subgroup.mem_map_of_mem π hx
    rw [hbot] at hxM
    have hx1 : π x = 1 := by simpa using hxM
    have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr hx1
    simpa [π, QuotientGroup.ker_mk'] using hxker
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
    · exact absurd hbot hMne
    · exact htop
  refine top_le_iff.mp ?_
  intro x hx
  have hxM : π x ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxM
  have hdiff : x * c⁻¹ ∈ QL := by
    have h1 : π (x * c⁻¹) = 1 := by rw [map_mul, map_inv, ← hcx, mul_inv_cancel]
    have h2 : x * c⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr h1
    simpa [π, QuotientGroup.ker_mk'] using h2
  have hmem1 : x * c⁻¹ ∈ C := hQC hdiff
  have hxeq : x = (x * c⁻¹) * c := by group
  rw [hxeq]
  exact C.mul_mem hmem1 hc

private theorem K_le_centralizer_Z_of_Zt_eq_bot (Y : Setup Γ G) {i : ℤ} (h : Y.Zt i = ⊥) :
    Y.K ≤ Subgroup.centralizer (Y.Z i : Set G) := by
  unfold Setup.Zt at h
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

private theorem Z_zero_eq_centerOf_L_zero_of_Zt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Z 0 = centerOf (Y.L 0) := by
  have hQ0L : Y.Q 0 ≤ Y.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 0))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.Gi 0))
  have hZ0L : Y.Z 0 ≤ Y.L 0 := (Y.Z_le_Q 0).trans hQ0L
  set CL : Subgroup ↥(Y.L 0) := (Y.L 0 ⊓ Subgroup.centralizer (Y.Z 0 : Set G)).subgroupOf (Y.L 0)
    with hCLdef
  set QL : Subgroup ↥(Y.L 0) := (Y.Q 0).subgroupOf (Y.L 0) with hQLdef
  have hLnormQ : Y.L 0 ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
    (Y.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hQLnormal : QL.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLnormQ
  haveI : QL.Normal := hQLnormal
  have hN : IsLocL2 Γ G (Y.vert 0) (Y.n 0) (Y.L 0) := Y.hyp.isLocL2_oTwoPrime (Y.vert 0)
  have hqeq : QL = CFSG.pCore 2 ↥(Y.L 0) := by
    rw [hQLdef, ← CFSG.openPCoreOf_subgroupOf 2 (Y.L 0), hN.pCoreOf_eq]
  have h2n : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  have hcardF : 4 ≤ Nat.card (GaloisField 2 (Y.n 0)) := by
    rw [GaloisField.card (p := 2) (n := Y.n 0) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Y.n 0 := Nat.pow_le_pow_right (by norm_num) h2n
  obtain ⟨e⟩ := hN.quot
  haveI hsimplePSL : IsSimpleGroup (PSL(2, GaloisField 2 (Y.n 0))) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  haveI hsimplePcore : IsSimpleGroup (↥(Y.L 0) ⧸ CFSG.pCore 2 ↥(Y.L 0)) :=
    e.isSimpleGroup_congr.mpr hsimplePSL
  haveI hsimpleQ : IsSimpleGroup (↥(Y.L 0) ⧸ QL) :=
    (QuotientGroup.quotientMulEquivOfEq hqeq.symm).isSimpleGroup_congr.mp hsimplePcore
  have hLnormZ : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Y.Z_normal 0 g (Y.L_le_Gi 0 hg))
  have hCLnormal : CL.Normal := by
    rw [hCLdef]
    exact subgroupOf_inf_centralizer_normal hZ0L hLnormZ
  haveI : CL.Normal := hCLnormal
  have hKCL : Y.K ≤ Y.L 0 ⊓ Subgroup.centralizer (Y.Z 0 : Set G) := by
    refine le_inf (Y.K_le_L_zero H) ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    simpa [Setup.Zt] using hZ
  have hKCL' : Y.K.subgroupOf (Y.L 0) ≤ CL := Subgroup.subgroupOf_mono _ hKCL
  have hQCL : QL ≤ CL := by
    intro q hq
    rw [hQLdef] at hq
    have hqQ : (q : G) ∈ Y.Q 0 := Subgroup.mem_subgroupOf.mp hq
    rw [hCLdef]
    refine Subgroup.mem_subgroupOf.mpr ⟨q.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 0 hz).2 q hqQ).symm
  have hKnotQL : ¬ Y.K.subgroupOf (Y.L 0) ≤ QL := by
    intro hle
    have hKQ0 : Y.K ≤ Y.Q 0 := by
      intro k hk
      have hkL : k ∈ Y.L 0 := Y.K_le_L_zero H hk
      have hkmem : (⟨k, hkL⟩ : ↥(Y.L 0)) ∈ Y.K.subgroupOf (Y.L 0) :=
        Subgroup.mem_subgroupOf.mpr hk
      exact Subgroup.mem_subgroupOf.mp (hle hkmem)
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.K) (B := Y.Q 0) Y.odd_card_K
      (pCoreOf_isPGroup' (Y.Gi 0))
    rw [inf_eq_left.mpr hKQ0] at hbot
    exact Y.K_ne_bot H hbot
  have hCLtop : CL = ⊤ :=
    eq_top_of_Q_zero_le_of_normal Y H hQCL (fun hle => hKnotQL (hKCL'.trans hle))
  have hL0CL : Y.L 0 ≤ Y.L 0 ⊓ Subgroup.centralizer (Y.Z 0 : Set G) := by
    intro x hx
    have hxCL : (⟨x, hx⟩ : ↥(Y.L 0)) ∈ CL := by
      rw [hCLtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxCL
  refine le_antisymm ?_ (Y.centerOf_L_le_Z H.char 0)
  refine le_inf hZ0L ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hL0CL hl).2 z hz).symm

private theorem center_S_eq_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hZ0L0 : Y.Z 0 = centerOf (Y.L 0)) : centerOf Y.S = Y.Z 0 := by
  have hSL : Y.S ≤ Y.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 0 ⊓ Y.Gi 1))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.Gi 0 ⊓ Y.Gi 1)).trans inf_le_left)
  have hZ0C : Y.Z 0 ≤ Subgroup.centralizer (Y.S : Set G) := by
    intro z hz
    have hz' : z ∈ centerOf (Y.L 0) := hZ0L0 ▸ hz
    have hzL : z ∈ Y.L 0 := (Subgroup.mem_inf.mp hz').1
    have hzcen : z ∈ Subgroup.centralizer (Y.L 0 : Set G) := (Subgroup.mem_inf.mp hz').2
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp hzcen s (hSL hs)
  have hEq := (Y.center_S_le_Z H 0 (Or.inl rfl)).2
  rw [inf_eq_left.mpr hZ0C] at hEq
  exact hEq.symm

private theorem center_L_one_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hZ0L0 : Y.Z 0 = centerOf (Y.L 0)) (h2 : centerOf Y.S = Y.Z 0) :
    centerOf (Y.L 1) = ⊥ := by
  have hQ1p : IsPGroup 2 (Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
  have hQ1le : Y.Q 1 ≤ Y.Gi 0 ⊓ Y.Gi 1 := by
    refine le_inf ?_ (Y.Q_le_Gi 1)
    intro x hx
    have h := Y.Q_le_Gi_adj 1 hx
    rw [show (1 : ℤ) - 1 = 0 by norm_num] at h
    exact h.1
  have hQ1norm : Y.Gi 0 ⊓ Y.Gi 1 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  have hQ1S : Y.Q 1 ≤ Y.S :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hQ1le
      (Subgroup.normal_subgroupOf_of_le_normalizer hQ1norm) hQ1p
  have hZL1S : centerOf (Y.L 1) ≤ Y.S :=
    ((Y.centerOf_L_le_Z H.char 1).trans (Y.Z_le_Q 1)).trans hQ1S
  have hSL : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hZL1C : centerOf (Y.L 1) ≤ Subgroup.centralizer (Y.S : Set G) := by
    intro z hz
    have hz' : z ∈ centerOf (Y.L 1) := hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 s (hSL hs)
  have hZL1Z0 : centerOf (Y.L 1) ≤ Y.Z 0 := by
    rw [← h2]
    exact le_inf hZL1S hZL1C
  have hZL1L0 : centerOf (Y.L 1) ≤ Y.L 0 :=
    hZL1Z0.trans ((Y.Z_le_Q 0).trans
      (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 0))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.Gi 0))))
  have hZL1L1 : centerOf (Y.L 1) ≤ Y.L 1 := inf_le_left
  have hcenL0 : centerOf (Y.L 1) ≤ centerOf (Y.L 0) := hZL1Z0.trans_eq hZ0L0
  have hnL0 : ((centerOf (Y.L 1)).subgroupOf (Y.L 0)).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ centerOf (Y.L 0) := hcenL0 (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx').2 (y : G) y.2)
  have hnL1 : ((centerOf (Y.L 1)).subgroupOf (Y.L 1)).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ centerOf (Y.L 1) := Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx').2 (y : G) y.2)
  exact eq_bot_of_normal_in_oTwoPrime Y.hyp (Y.adj 0) hZL1L0 hnL0 hZL1L1 hnL1

private theorem relIndex_Q_one_L_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Q 1).relIndex (Y.L 1) = 6 := by
  have hN1 : IsLocL2 Γ G (Y.vert 1) (Y.n 1) (Y.L 1) := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  obtain ⟨e⟩ := hN1.quot
  have hQeq : (Y.Q 1).subgroupOf (Y.L 1) = CFSG.pCore 2 ↥(Y.L 1) := by
    rw [show Y.Q 1 = pCoreOf 2 (Y.L 1) from hN1.pCoreOf_eq.symm,
      CFSG.openPCoreOf_subgroupOf]
  have hcard : Nat.card (↥(Y.L 1) ⧸ CFSG.pCore 2 ↥(Y.L 1)) = 6 := by
    rw [Nat.card_congr e.toEquiv, H.n_one, card_psl_two_gf2_one]
  have hindex : ((Y.Q 1).subgroupOf (Y.L 1)).index = 6 := by
    rw [Subgroup.index_eq_card, hQeq]
    exact hcard
  simpa [Subgroup.relIndex] using hindex

private theorem Z_zero_le_Q_one_of_center (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hZ0L0 : Y.Z 0 = centerOf (Y.L 0)) (hZL1 : centerOf (Y.L 1) = ⊥) : Y.Z 0 ≤ Y.Q 1 := by
  classical
  have hQ1L : Y.Q 1 ≤ Y.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 1)) (Y.Q_le_Gi 1)
  have hQ1G0 : Y.Q 1 ≤ Y.Gi 0 := by
    intro x hx
    have h := Y.Q_le_Gi_adj 1 hx
    rw [show (1 : ℤ) - 1 = 0 by norm_num] at h
    exact h.1
  have hQ1L0 : Y.Q 1 ≤ Y.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 1)) hQ1G0
  have hZ1L0 : Y.Z 1 ≤ Y.L 0 := (Y.Z_le_Q 1).trans hQ1L0
  have hZ1L1 : Y.Z 1 ≤ Y.L 1 := (Y.Z_le_Q 1).trans hQ1L
  have hZ0G1 : Y.Z 0 ≤ Y.Gi 1 := by
    intro x hx
    have h := Y.Q_le_Gi_adj 0 (Y.Z_le_Q 0 hx)
    rw [show (0 : ℤ) + 1 = 1 by norm_num] at h
    exact h.2
  have hZ0L1 : Y.Z 0 ≤ Y.L 1 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0)) hZ0G1
  set C : Subgroup G := Y.L 1 ⊓ Subgroup.centralizer (Y.Z 1 : Set G) with hCdef
  have hQ1C : Y.Q 1 ≤ C := by
    refine le_inf hQ1L ?_
    intro q hq
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Y.Z_le_center 1 hz)).2 q hq).symm
  have hZ0C : Y.Z 0 ≤ C := by
    refine le_inf hZ0L1 ?_
    intro z hz
    have hz' : z ∈ centerOf (Y.L 0) := hZ0L0 ▸ hz
    have hzcen : z ∈ Subgroup.centralizer (Y.L 0 : Set G) := (Subgroup.mem_inf.mp hz').2
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z1 hz1
    exact Subgroup.mem_centralizer_iff.mp hzcen z1 (hZ1L0 hz1)
  have hL1normZ1 : Y.L 1 ≤ Subgroup.normalizer (Y.Z 1 : Set G) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Y.Z_normal 1 g (Y.L_le_Gi 1 hg))
  have hZ1normal : ((Y.Z 1).subgroupOf (Y.L 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL1normZ1
  have hCnormal : (C.subgroupOf (Y.L 1)).Normal := by
    rw [hCdef]
    exact subgroupOf_inf_centralizer_normal hZ1L1 hL1normZ1
  have hCL : C ≤ Y.L 1 := inf_le_left
  have hrel : (Y.Q 1).relIndex (Y.L 1) = 6 := relIndex_Q_one_L_one Y H
  have hmul : (Y.Q 1).relIndex C * C.relIndex (Y.L 1) = 6 := by
    rw [Subgroup.relIndex_mul_relIndex (H := Y.Q 1) (K := C) (L := Y.L 1) hQ1C hCL, hrel]
  set a : ℕ := (Y.Q 1).relIndex C with ha_def
  have ha_dvd : a ∣ 6 := ⟨C.relIndex (Y.L 1), hmul.symm⟩
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      rw [h, zero_mul] at hmul
      exact absurd hmul (by norm_num)
    · exact h
  have ha_le : a ≤ 6 := Nat.le_of_dvd (by norm_num) ha_dvd
  haveI : Finite ↥C := finite_of_le_stabilizer Y.hyp (hCL.trans (Y.L_le_Gi 1))
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (hQ1L.trans (Y.L_le_Gi 1))
  set Qc : Subgroup ↥C := (Y.Q 1).subgroupOf C with hQc_def
  have hQcNormal : Qc.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    exact hCL.trans ((Y.L_le_Gi 1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)))
  have hodd : ¬ 2 ∣ a → Y.Z 0 ≤ Y.Q 1 := fun h2 =>
    le_of_normal_isSylowTwoOf (F7.isSylowTwoOf_of_relIndex hQ1C (pCoreOf_isPGroup' (Y.Gi 1)) h2)
      hQcNormal hZ0C ((pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0))
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  rcases hcases with h | h | h | h | h | h
  · exact hodd (by rw [h]; norm_num)
  ·
    exfalso
    have h2 : (Y.Q 1).relIndex C = 2 := by rw [← ha_def]; exact h
    have hcardC : Nat.card C = 2 * Nat.card (Y.Q 1) := by
      have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := C)
      rw [show Y.Q 1 ⊓ C = Y.Q 1 from inf_eq_left.mpr hQ1C, h2] at h
      exact h.symm
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup' (Y.Gi 1)).exists_card_eq
    have hCp : IsPGroup 2 C := IsPGroup.of_card (by rw [hcardC, hk, mul_comm, ← pow_succ])
    have hcle : C ≤ Y.Q 1 := by
      have h := CFSG.LieType.BorelTits.le_pCoreOf 2 hCL hCnormal hCp
      rwa [show pCoreOf 2 (Y.L 1) = Y.Q 1 from
        (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).pCoreOf_eq] at h
    have h1 : (Y.Q 1).relIndex C = 1 := Subgroup.relIndex_eq_one.mpr hcle
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  ·
    have h3 : (Y.Q 1).relIndex C = 3 := by rw [← ha_def]; exact h
    haveI : Qc.Normal := hQcNormal
    let π : ↥C →* (↥C ⧸ Qc) := QuotientGroup.mk' Qc
    have hcardquot : Nat.card (↥C ⧸ Qc) = 3 := by
      have h := Subgroup.index_eq_card Qc
      rw [← h]
      exact h3
    have h2Z0 : IsPGroup 2 (Y.Z 0) := (pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0)
    have h2img : IsPGroup 2 (((Y.Z 0).subgroupOf C).map π) :=
      (h2Z0.comap_of_injective C.subtype C.subtype_injective).map π
    have hdiv : Nat.card (((Y.Z 0).subgroupOf C).map π) ∣ Nat.card (↥C ⧸ Qc) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hcardquot] at hdiv
    obtain ⟨k, hk⟩ := h2img.exists_card_eq
    have hk0 : k = 0 := by
      have hdvd : 2 ^ k ∣ 3 := hk ▸ hdiv
      rcases Nat.dvd_prime (by norm_num : Nat.Prime 3) |>.mp hdvd with h | h
      · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exact hk0
        · exfalso
          have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hkpos.ne'
          rw [h] at h2
          norm_num at h2
      · exfalso
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0] at h
          norm_num at h
        · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hkpos.ne'
          rw [h] at h2
          norm_num at h2
    have hbot : ((Y.Z 0).subgroupOf C).map π = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
    intro z hz
    have hzC : z ∈ C := hZ0C hz
    have hzsub : (⟨z, hzC⟩ : ↥C) ∈ (Y.Z 0).subgroupOf C := Subgroup.mem_subgroupOf.mpr hz
    have hzimg : π ⟨z, hzC⟩ ∈ ((Y.Z 0).subgroupOf C).map π := Subgroup.mem_map_of_mem π hzsub
    rw [hbot] at hzimg
    have hz1 : π ⟨z, hzC⟩ = 1 := by simpa using hzimg
    have hzker : (⟨z, hzC⟩ : ↥C) ∈ π.ker := MonoidHom.mem_ker.mpr hz1
    have hzQ : (⟨z, hzC⟩ : ↥C) ∈ Qc := by
      simpa [π, QuotientGroup.ker_mk'] using hzker
    exact Subgroup.mem_subgroupOf.mp hzQ
  ·
    exfalso
    rw [h] at ha_dvd
    norm_num at ha_dvd
  · exact hodd (by rw [h]; norm_num)
  ·
    exfalso
    have hb : C.relIndex (Y.L 1) = 1 := by
      rw [h] at hmul
      omega
    have hLC : Y.L 1 ≤ C := Subgroup.relIndex_eq_one.mp hb
    have hZ1Z : Y.Z 1 ≤ centerOf (Y.L 1) := by
      refine le_inf hZ1L1 ?_
      intro z hz
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro l hl
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hLC hl)).2 z hz).symm
    rw [hZL1] at hZ1Z
    have hbot : Y.Z 1 = ⊥ := le_bot_iff.mp hZ1Z
    exact Y.Z_ne_bot_of 1 (Y.Q_ne_bot H.char 1) hbot

private theorem Z_two_eq_center_L_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Z 2 = centerOf (Y.L 2) := by
  have h1 := Z_zero_eq_centerOf_L_zero_of_Zt Y H hZ
  have hZeq : Y.Z 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 0) := by
    rw [show (2 : ℤ) = 0 + 2 * (1 : ℤ) by norm_num, Y.Z_add]
  have hL2 : conjSub (Y.τ ^ (1 : ℤ)) (Y.L 0) = Y.L 2 := by
    rw [show conjSub (Y.τ ^ (1 : ℤ)) (Y.L 0) = Y.L (0 + 2 * (1 : ℤ)) from
      (Y.L_add (1 : ℤ) 0).symm]
    norm_num
  calc Y.Z 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 0) := hZeq
    _ = conjSub (Y.τ ^ (1 : ℤ)) (centerOf (Y.L 0)) := congrArg (conjSub (Y.τ ^ (1 : ℤ))) h1
    _ = centerOf (conjSub (Y.τ ^ (1 : ℤ)) (Y.L 0)) := (centerOf_conjSub _ _).symm
    _ = centerOf (Y.L 2) := by rw [hL2]

private theorem mirror1_Zt_zero_and_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    (Y.mirror1).Zt 0 = ⊥ ∧ (Y.mirror1).Z 0 = centerOf ((Y.mirror1).L 0) :=
  ⟨by simpa [Setup.Zt] using Zt_eq_bot_of_even Y hZ even_two,
   by simpa using Z_two_eq_center_L_two Y H hZ⟩

private theorem center_edgeSylow_one_eq_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : centerOf (Y.edgeSylow 1) = Y.Z 2 := by
  obtain ⟨hZt2', hcen2'⟩ := mirror1_Zt_zero_and_Z_zero Y H hZ
  have h2' : centerOf (Y.mirror1).S = (Y.mirror1).Z 0 :=
    center_S_eq_Z_zero Y.mirror1 H.mirror1 hZt2' hcen2'
  have hS2eq : (Y.mirror1).S = Y.edgeSylow 1 := by
    rw [show (Y.mirror1).S = pCoreOf 2 ((Y.mirror1).Gi 0 ⊓ (Y.mirror1).Gi 1) from rfl,
      Setup.mirror1_Gi, Setup.mirror1_Gi]
    rw [show (2 : ℤ) - 0 = 2 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num]
    rw [inf_comm]
    rfl
  rw [← hS2eq, h2', Setup.mirror1_Z]
  norm_num

private theorem Z_two_le_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 2 ≤ Y.Q 1 := by
  obtain ⟨hZt2', hcen2'⟩ := mirror1_Zt_zero_and_Z_zero Y H hZ
  have h2' : centerOf (Y.mirror1).S = (Y.mirror1).Z 0 :=
    center_S_eq_Z_zero Y.mirror1 H.mirror1 hZt2' hcen2'
  have h3' : centerOf ((Y.mirror1).L 1) = ⊥ :=
    center_L_one_eq_bot Y.mirror1 H.mirror1 hZt2' hcen2' h2'
  exact Z_zero_le_Q_one_of_center Y.mirror1 H.mirror1 hZt2' hcen2' h3'

private theorem isSylowTwoOf_S_Gi_one (Y : Setup Γ G) : IsSylowTwoOf Y.S (Y.Gi 1) := by
  have hSsyl0 : IsSylowTwoOf Y.S (Y.Gi 0 ⊓ Y.Gi 1) := by
    simpa [Setup.S, Setup.edgeSylow] using Y.isSylowTwoOf_edgeSylow 0
  exact isSylowTwoOf_of_edgeStab Y.hyp (α := Y.vert 1) (β := Y.vert 0) (Y.adj 0).symm
    (by simpa [inf_comm] using hSsyl0)

private theorem Z_zero_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) (h4 : Y.Z 0 ≤ Y.Q 1) : Y.Z 0 ≤ Y.Z 1 := by
  have hSsyl1 : IsSylowTwoOf Y.S (Y.Gi 1) := isSylowTwoOf_S_Gi_one Y
  have hsum : centerOf Y.S ⊓ Y.Q 1 = Y.Z 0 := by rw [h2, inf_eq_left.mpr h4]
  have hle := le_iSup₂_of_le
    (f := fun P (_ : IsSylowTwoOf P (Y.Gi 1)) => centerOf P ⊓ Y.Q 1)
    (a := centerOf Y.S ⊓ Y.Q 1) Y.S hSsyl1 le_rfl
  rw [hsum] at hle
  exact hle

private theorem Z_two_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 2 ≤ Y.Z 1 := by
  have hcenS2 : centerOf (Y.edgeSylow 1) = Y.Z 2 := center_edgeSylow_one_eq_Z_two Y H hZ
  have hS2syl1 : IsSylowTwoOf (Y.edgeSylow 1) (Y.Gi 1) :=
    isSylowTwoOf_of_edgeStab Y.hyp (Y.adj 1) (Y.isSylowTwoOf_edgeSylow 1)
  have hZ2Q1 : Y.Z 2 ≤ Y.Q 1 := Z_two_le_Q_one Y H hZ
  have hsum : centerOf (Y.edgeSylow 1) ⊓ Y.Q 1 = Y.Z 2 := by
    rw [hcenS2, inf_eq_left.mpr hZ2Q1]
  have hle := le_iSup₂_of_le
    (f := fun P (_ : IsSylowTwoOf P (Y.Gi 1)) => centerOf P ⊓ Y.Q 1)
    (a := centerOf (Y.edgeSylow 1) ⊓ Y.Q 1) (Y.edgeSylow 1) hS2syl1 le_rfl
  rw [hsum] at hle
  exact hle

private theorem Z_one_eq_iSup_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) (h4 : Y.Z 0 ≤ Y.Q 1) :
    (⨆ g ∈ Y.L 1, (Y.Z 0).map (MulAut.conj g).toMonoidHom) = Y.Z 1 := by
  classical
  haveI hfin1 : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := Z_zero_le_Z_one Y H hZ h2 h4
  refine le_antisymm ?_ ?_
  · refine iSup_le fun g => iSup_le fun hg => ?_
    calc (Y.Z 0).map (MulAut.conj g).toMonoidHom = conjSub g (Y.Z 0) := rfl
      _ ≤ conjSub g (Y.Z 1) := conjSub_mono g hZ0Z1
      _ = Y.Z 1 := Y.Z_normal 1 g (Y.L_le_Gi 1 hg)
  · rw [Setup.Z]
    refine iSup_le fun P => iSup_le fun hP => ?_
    intro x hx
    obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hSsyl1 : IsSylowTwoOf Y.S (Y.Gi 1) := isSylowTwoOf_S_Gi_one Y
    obtain ⟨c, hcG1, hcP⟩ :=
      CFSG.Quasithin.RonanF713.isSylowTwoOf_exists_conj_le_loc hSsyl1 hP.1 hP.2.1
    have hcPsyl : IsSylowTwoOf (conjSub c Y.S) (Y.Gi 1) := by
      have h := F7.isSylowTwoOf_conj hSsyl1 c
      rwa [conjSub_eq_of_mem hcG1] at h
    haveI hfinS : Finite ↥(conjSub c Y.S) := finite_of_le_stabilizer Y.hyp hcPsyl.1
    have hPeq : P = conjSub c Y.S :=
      (CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hP hcPsyl.2.1 hcPsyl.1 hcP).symm
    rw [hPeq] at hxP
    have hxconj : x ∈ conjSub c (Y.Z 0) := by
      have hcen : centerOf (conjSub c Y.S) = conjSub c (centerOf Y.S) := centerOf_conjSub c Y.S
      rw [hcen, h2] at hxP
      exact hxP
    have hfratt : ((Y.L 1).subgroupOf (Y.Gi 1)) ⊔ ((Y.Gi 1 ⊓ Y.Gi 0).subgroupOf (Y.Gi 1)) =
        ⊤ := by
      have h : (Y.Gi 1 ⊓ Y.Gi 0) ⊔ Y.L 1 = Y.Gi 1 := frattini_oTwoPrime Y.hyp (Y.adj 0).symm
      rw [sup_comm]
      rw [← Subgroup.subgroupOf_sup (A := Y.Gi 1 ⊓ Y.Gi 0) (A' := Y.L 1)
        (B := Y.Gi 1) inf_le_left (Y.L_le_Gi 1), h, Subgroup.subgroupOf_self]
    have hc : (⟨c, hcG1⟩ : ↥(Y.Gi 1)) ∈ ⊤ := Subgroup.mem_top _
    rw [← hfratt] at hc
    haveI hL1n : ((Y.L 1).subgroupOf (Y.Gi 1)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoPrime (Y.Gi 1))
    rw [Subgroup.mem_sup_of_normal_left] at hc
    obtain ⟨l, hl, a, ha, hla⟩ := hc
    have hlL : (l : G) ∈ Y.L 1 := Subgroup.mem_subgroupOf.mp hl
    have haA : (a : G) ∈ Y.Gi 1 ⊓ Y.Gi 0 := Subgroup.mem_subgroupOf.mp ha
    have hceq : (l : G) * (a : G) = c := by
      simpa using congrArg Subtype.val hla
    have haZ : conjSub (a : G) (Y.Z 0) = Y.Z 0 :=
      Y.Z_normal 0 (a : G) haA.2
    have hcZ : conjSub c (Y.Z 0) = conjSub (l : G) (Y.Z 0) := by
      rw [← hceq, conjSub_mul, haZ]
    rw [hcZ] at hxconj
    exact le_iSup₂_of_le
      (f := fun g (_ : g ∈ Y.L 1) => (Y.Z 0).map (MulAut.conj g).toMonoidHom)
      (a := (Y.Z 0).map (MulAut.conj (l : G)).toMonoidHom) (l : G) hlL le_rfl hxconj

private theorem card_Z_zero_and_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) (h5 : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2) (h6 : Y.Z 0 ⊓ Y.Z 2 = ⊥) :
    Nat.card (Y.Z 0) = 2 ∧ Y.Zt 1 = ⊥ := by
  have hZt2 : Y.Zt 2 = ⊥ := Zt_eq_bot_of_even Y hZ even_two
  have hKZ0 : Y.K ≤ Subgroup.centralizer (Y.Z 0 : Set G) :=
    K_le_centralizer_Z_of_Zt_eq_bot Y hZ
  have hKZ2 : Y.K ≤ Subgroup.centralizer (Y.Z 2 : Set G) :=
    K_le_centralizer_Z_of_Zt_eq_bot Y hZt2
  have hKZ1 : Y.K ≤ Subgroup.centralizer (Y.Z 1 : Set G) := by
    rw [h5]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hKZ0 hKZ2
  have hZt1 : Y.Zt 1 = ⊥ := by
    unfold Setup.Zt
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKZ1
  refine ⟨?_, hZt1⟩
  have hcard2 : Nat.card (Y.Z 2) = Nat.card (Y.Z 0) := by
    have hZ2 : Y.Z 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 0) := by
      rw [show (2 : ℤ) = 0 + 2 * (1 : ℤ) by norm_num, Y.Z_add]
    rw [hZ2, card_conjSub]
  have hZ2Q1 : Y.Z 2 ≤ Y.Q 1 := Z_two_le_Q_one Y H hZ
  have hnorm : Y.Z 2 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := by
    refine (show Y.Z 2 ≤ Subgroup.centralizer (Y.Z 0 : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer (Y.Z 0 : Set G))
    intro b hb
    have hbS : b ∈ Y.S := by
      rw [show Y.S = Y.edgeSylow 0 from Y.edgeSylow_zero.symm, ← Y.sup_Q_eq_edgeSylow H.char 0]
      exact Subgroup.mem_sup_right (hZ2Q1 hb)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haS : a ∈ centerOf Y.S := by rw [h2]; exact ha
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haS).2 b hbS).symm
  have hcardZ1 : Nat.card (Y.Z 1) = Nat.card (Y.Z 0) * Nat.card (Y.Z 0) := by
    rw [h5, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      hnorm (disjoint_iff.mpr h6), hcard2]
  have hZ1Qs : Y.Z 1 ≤ Y.Qs 1 := by
    refine le_inf (Y.Z_le_Q 1) ?_
    have h := hZt1
    unfold Setup.Zt at h
    rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  haveI : Finite ↥(Y.Qs 1) :=
    finite_of_le_stabilizer Y.hyp (inf_le_left.trans (Y.Q_le_Gi 1))
  have hcardZ1le : Nat.card (Y.Z 1) ≤ 8 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hZ1Qs)
      (Subgroup.inclusion_injective hZ1Qs)).trans (Y.card_Qs_le H)
  have hZ0ne : Y.Z 0 ≠ ⊥ := Y.Z_ne_bot_of 0 (Y.Q_ne_bot H.char 0)
  haveI : Finite ↥(Y.Z 0) := finite_of_le_stabilizer Y.hyp ((Y.Z_le_Q 0).trans (Y.Q_le_Gi 0))
  have hZ0pos : 0 < Nat.card (Y.Z 0) := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hZ0p : IsPGroup 2 (Y.Z 0) := (pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0)
  obtain ⟨k, hk⟩ := hZ0p.exists_card_eq
  have hk2 : 2 ^ k * 2 ^ k ≤ 8 := by
    rw [hcardZ1, hk] at hcardZ1le
    exact hcardZ1le
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, pow_zero] at hk
      exact hZ0ne (Subgroup.card_eq_one.mp hk)
    · exact h
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · omega
    · exfalso
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      have h16 : 16 ≤ 2 ^ k * 2 ^ k := by
        calc 16 = 4 * 4 := by norm_num
          _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul h4 h4
      omega
  rw [hk, hk1]
  norm_num

private theorem conj_eq_of_smul_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) {g g' : G} (hg : g ∈ Y.L 1) (hg' : g' ∈ Y.L 1)
    (h : g • Y.vert 0 = g' • Y.vert 0) {u : G} (hu : u ∈ Y.Z 0) :
    g * u * g⁻¹ = g' * u * g'⁻¹ := by
  have hfix : (g'⁻¹ * g) • Y.vert 0 = Y.vert 0 := by
    rw [mul_smul, h, inv_smul_smul]
  have hmem : g'⁻¹ * g ∈ Y.L 1 ⊓ Y.Gi 0 :=
    ⟨(Y.L 1).mul_mem ((Y.L 1).inv_mem hg') hg, MulAction.mem_stabilizer_iff.mpr hfix⟩
  have hS := Y.L_one_inf_Gi_zero_le_S H hmem
  have hSZ : Y.S ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact h2 ▸ (inf_le_right : centerOf Y.S ≤ Subgroup.centralizer (Y.S : Set G))
  have hcent : (g'⁻¹ * g) * u * (g'⁻¹ * g)⁻¹ = u := by
    have hc := Subgroup.mem_centralizer_iff.mp (hSZ hS) u hu
    rw [← hc]
    group
  calc g * u * g⁻¹ = (g' * (g'⁻¹ * g)) * u * (g' * (g'⁻¹ * g))⁻¹ := by group
    _ = g' * ((g'⁻¹ * g) * u * (g'⁻¹ * g)⁻¹) * g'⁻¹ := by group
    _ = g' * u * g'⁻¹ := by rw [hcent]


theorem exists_third_nbr (Y : Setup Γ G) :
    ∃ c : V, Γ.Adj (Y.vert 1) c ∧ c ≠ Y.vert 0 ∧ c ≠ Y.vert 2 :=
  exists_adj_ne_ne (v := Y.vert 1) (a := Y.vert 0) (b := Y.vert 2)
    (Y.hyp.three_le_card (Y.vert 1))

theorem adj_one_zero (Y : Setup Γ G) : Γ.Adj (Y.vert 1) (Y.vert 0) :=
  (Y.adj 0).symm

theorem adj_one_two (Y : Setup Γ G) : Γ.Adj (Y.vert 1) (Y.vert 2) := by
  simpa using Y.adj 1

theorem vert_zero_ne_vert_two (Y : Setup Γ G) : Y.vert 0 ≠ Y.vert 2 := by
  intro h
  have := Y.vert_injective h
  omega

theorem eq_of_adj_one_of_ne (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {v w : V}
    (hv : Γ.Adj (Y.vert 1) v) (hw : Γ.Adj (Y.vert 1) w)
    (hv0 : v ≠ Y.vert 0) (hv2 : v ≠ Y.vert 2)
    (hw0 : w ≠ Y.vert 0) (hw2 : w ≠ Y.vert 2) : v = w := by
  classical
  have hfin : (Γ.neighborSet (Y.vert 1)).Finite := Y.hyp.finite_neighborSet (Y.vert 1)
  have h02 : Y.vert 0 ≠ Y.vert 2 := vert_zero_ne_vert_two Y
  have hinter : (Γ.neighborSet (Y.vert 1) ∩ {Y.vert 0, Y.vert 2}).ncard = 2 := by
    have hsub : ({Y.vert 0, Y.vert 2} : Set V) ⊆ Γ.neighborSet (Y.vert 1) := by
      intro z hz
      rcases (by simpa using hz : z = Y.vert 0 ∨ z = Y.vert 2) with rfl | rfl
      · exact (SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) (Y.vert 0)).mpr (adj_one_zero Y)
      · exact (SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) (Y.vert 2)).mpr (adj_one_two Y)
    rw [Set.inter_eq_right.mpr hsub]
    exact Set.ncard_pair h02
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (s := Γ.neighborSet (Y.vert 1)) (t := ({Y.vert 0, Y.vert 2} : Set V)) hfin
  have hcomp : (Γ.neighborSet (Y.vert 1) \ {Y.vert 0, Y.vert 2}).ncard ≤ 1 := by
    rw [hinter, Y.ncard_neighborSet_one H] at hsum
    omega
  have hv' : v ∈ Γ.neighborSet (Y.vert 1) \ {Y.vert 0, Y.vert 2} := by
    refine ⟨(SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) v).mpr hv, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hv0, hv2⟩
  have hw' : w ∈ Γ.neighborSet (Y.vert 1) \ {Y.vert 0, Y.vert 2} := by
    refine ⟨(SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) w).mpr hw, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hw0, hw2⟩
  exact (Set.ncard_le_one (s := Γ.neighborSet (Y.vert 1) \ {Y.vert 0, Y.vert 2})
    hfin.sdiff).mp hcomp v hv' w hw'

theorem smul_third_of_smul_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {k : G}
    (hk : k ∈ Y.Gi 1) {c : V} (hc : Γ.Adj (Y.vert 1) c) (hc0 : c ≠ Y.vert 0)
    (hc2 : c ≠ Y.vert 2) (hk0 : k • Y.vert 0 = Y.vert 0) :
    (k • Y.vert 2 = Y.vert 2 → k • c = c) ∧
      (k • Y.vert 2 = c → k • c = Y.vert 2) := by
  have hkc : Γ.Adj (Y.vert 1) (k • c) := by
    have h := (Y.hyp.adj_smul k (Y.vert 1) c).mpr hc
    rwa [MulAction.mem_stabilizer_iff.mp hk] at h
  have hkc0 : k • c ≠ Y.vert 0 := by
    intro h
    exact hc0 (MulAction.injective k (h.trans hk0.symm))
  constructor
  · intro h2
    refine eq_of_adj_one_of_ne Y H hkc hc hkc0 ?_ hc0 hc2
    intro h2'
    exact hc2 (MulAction.injective k (h2'.trans h2.symm))
  · intro h2
    by_contra hne
    have hfix : k • c = c :=
      eq_of_adj_one_of_ne Y H hkc hc hkc0 hne hc0 hc2
    exact hc2 (MulAction.injective k (h2.trans hfix.symm)).symm

theorem smul_third_of_smul_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {k : G}
    (hk : k ∈ Y.Gi 1) {c : V} (hc : Γ.Adj (Y.vert 1) c) (hc0 : c ≠ Y.vert 0)
    (hc2 : c ≠ Y.vert 2) (hk2 : k • Y.vert 2 = Y.vert 2) :
    (k • Y.vert 0 = Y.vert 0 → k • c = c) ∧
      (k • Y.vert 0 = c → k • c = Y.vert 0) := by
  have hkc : Γ.Adj (Y.vert 1) (k • c) := by
    have h := (Y.hyp.adj_smul k (Y.vert 1) c).mpr hc
    rwa [MulAction.mem_stabilizer_iff.mp hk] at h
  have hkc2 : k • c ≠ Y.vert 2 := by
    intro h
    exact hc2 (MulAction.injective k (h.trans hk2.symm))
  constructor
  · intro h0
    refine eq_of_adj_one_of_ne Y H hkc hc ?_ hkc2 hc0 hc2
    intro h'
    exact hc0 (MulAction.injective k (h'.trans h0.symm))
  · intro h0
    by_contra hne
    have hfix : k • c = c :=
      eq_of_adj_one_of_ne Y H hkc hc hne hkc2 hc0 hc2
    exact hc0 (MulAction.injective k (h0.trans hfix.symm)).symm

private theorem conj_conj_eq_of_smul_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h2 : centerOf Y.S = Y.Z 0) {k g g' : G}
    (hk : k ∈ Y.L 1) (hg : g ∈ Y.L 1) (hg' : g' ∈ Y.L 1)
    (h : (k * g) • Y.vert 0 = g' • Y.vert 0) {u : G} (hu : u ∈ Y.Z 0) :
    k * (g * u * g⁻¹) * k⁻¹ = g' * u * g'⁻¹ := by
  have hkg : k * g ∈ Y.L 1 := (Y.L 1).mul_mem hk hg
  have hc := conj_eq_of_smul_eq Y H hZ h2 hkg hg' h hu
  calc k * (g * u * g⁻¹) * k⁻¹ = (k * g) * u * (k * g)⁻¹ := by group
    _ = g' * u * g'⁻¹ := hc

private theorem S_le_centralizer_mul_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h2 : centerOf Y.S = Y.Z 0) (h4 : Y.Z 0 ≤ Y.Q 1) {a b : G}
    (ha : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2) (hb : b ∈ Y.L 1)
    (hb0 : b • Y.vert 0 ≠ Y.vert 0) (hb2 : b • Y.vert 0 ≠ Y.vert 2) {u : G}
    (hu : u ∈ Y.Z 0) :
    Y.S ≤ Subgroup.centralizer ({u * (a * u * a⁻¹) * (b * u * b⁻¹)} : Set G) := by
  have hSleL1 : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hSfix0 : Y.S ≤ MulAction.stabilizer G (Y.vert 0) := by
    rw [← Y.edgeSylow_zero]
    exact (Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left
  have hSfix1 : Y.S ≤ MulAction.stabilizer G (Y.vert 1) := by
    rw [← Y.edgeSylow_zero]
    exact (Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right
  have hSZ0 : Y.S ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact h2 ▸ (inf_le_right : centerOf Y.S ≤ Subgroup.centralizer (Y.S : Set G))
  have hbadj : Γ.Adj (Y.vert 1) (b • Y.vert 0) := by
    have h := (Y.hyp.adj_smul b (Y.vert 1) (Y.vert 0)).mpr (adj_one_zero Y)
    rwa [MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 1 hb)] at h
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := Z_zero_le_Z_one Y H hZ h2 h4
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := Z_two_le_Z_one Y H hZ
  have hZa : conjSub a (Y.Z 0) = Y.Z 2 := by
    have h := vertZ_smul (G := G) a (Y.vert 0)
    rw [ha0] at h
    show conjSub a (vertZ (Y.vert 0)) = vertZ (Y.vert 2)
    exact h.symm
  have hZb1 : conjSub b (Y.Z 0) ≤ Y.Z 1 := by
    have h := Z_one_eq_iSup_conj Y H hZ h2 h4
    rw [← h]
    exact le_iSup₂_of_le b hb le_rfl
  have hZ1abel : ∀ p ∈ Y.Z 1, ∀ q ∈ Y.Z 1, p * q = q * p := Y.Z_commute 1
  have huZ : u ∈ Y.Z 1 := hZ0Z1 hu
  set x : G := a * u * a⁻¹ with hx
  set y : G := b * u * b⁻¹ with hy
  set σ : G := u * x * y with hσ
  have hxZ : x ∈ Y.Z 1 := by
    rw [hx]
    exact hZ2Z1 (hZa ▸ mul_mem_conjSub hu)
  have hyZ : y ∈ Y.Z 1 := by
    rw [hy]
    exact hZb1 (mul_mem_conjSub hu)
  intro k hk
  have hk0 : k • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp (hSfix0 hk)
  have hk1 : k • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp (hSfix1 hk)
  have hk2v : Γ.Adj (Y.vert 1) (k • Y.vert 2) := by
    have h := (Y.hyp.adj_smul k (Y.vert 1) (Y.vert 2)).mpr (adj_one_two Y)
    rwa [hk1] at h
  have hku : k * u * k⁻¹ = u := by
    have hc := Subgroup.mem_centralizer_iff.mp (hSZ0 hk) u hu
    rw [← hc]
    group
  have hk2case : k • Y.vert 2 = Y.vert 2 ∨ k • Y.vert 2 = b • Y.vert 0 := by
    have hne0 : k • Y.vert 2 ≠ Y.vert 0 := by
      intro h
      exact (vert_zero_ne_vert_two Y)
        (MulAction.injective k (h.trans hk0.symm)).symm
    by_cases h2' : k • Y.vert 2 = Y.vert 2
    · exact Or.inl h2'
    · exact Or.inr (eq_of_adj_one_of_ne Y H hk2v hbadj hne0 h2' hb0 hb2)
  have hkσ : k * σ = σ * k := by
    have hkσ' : k * σ * k⁻¹ = σ := by
      rcases hk2case with h2' | h2'
      · have hkx : k * x * k⁻¹ = x := by
          rw [hx]
          exact conj_conj_eq_of_smul_eq Y H hZ h2 (hSleL1 hk) ha ha
            (by rw [mul_smul, ha0, h2']) hu
        have hyb : k * y * k⁻¹ = y := by
          have hkb0 : (k * b) • Y.vert 0 = b • Y.vert 0 := by
            rw [mul_smul]
            exact (smul_third_of_smul_two Y H (Y.L_le_Gi 1 (hSleL1 hk)) hbadj hb0 hb2
              hk0).1 h2'
          have hkb : k * b ∈ Y.L 1 := (Y.L 1).mul_mem (hSleL1 hk) hb
          have hc := conj_eq_of_smul_eq Y H hZ h2 hkb hb hkb0 hu
          rw [hy]
          calc k * (b * u * b⁻¹) * k⁻¹ = (k * b) * u * (k * b)⁻¹ := by group
            _ = b * u * b⁻¹ := hc
        rw [hσ]
        calc k * (u * x * y) * k⁻¹ =
              (k * u * k⁻¹) * (k * x * k⁻¹) * (k * y * k⁻¹) := by group
          _ = u * x * y := by rw [hku, hkx, hyb]
      · have hkx : k * x * k⁻¹ = y := by
          have hka : k * a ∈ Y.L 1 := (Y.L 1).mul_mem (hSleL1 hk) ha
          have hka0 : (k * a) • Y.vert 0 = b • Y.vert 0 := by
            rw [mul_smul, ha0]
            exact h2'
          have hc := conj_eq_of_smul_eq Y H hZ h2 hka hb hka0 hu
          rw [hx, hy]
          calc k * (a * u * a⁻¹) * k⁻¹ = (k * a) * u * (k * a)⁻¹ := by group
            _ = b * u * b⁻¹ := hc
        have hky : k * y * k⁻¹ = x := by
          have hkb0 : (k * b) • Y.vert 0 = Y.vert 2 := by
            rw [mul_smul]
            exact (smul_third_of_smul_two Y H (Y.L_le_Gi 1 (hSleL1 hk)) hbadj hb0 hb2
              hk0).2 h2'
          have hkb : k * b ∈ Y.L 1 := (Y.L 1).mul_mem (hSleL1 hk) hb
          have hc := conj_eq_of_smul_eq Y H hZ h2 hkb ha (hkb0.trans ha0.symm) hu
          rw [hy, hx]
          calc k * (b * u * b⁻¹) * k⁻¹ = (k * b) * u * (k * b)⁻¹ := by group
            _ = a * u * a⁻¹ := hc
        rw [hσ]
        calc k * (u * x * y) * k⁻¹ =
              (k * u * k⁻¹) * (k * x * k⁻¹) * (k * y * k⁻¹) := by group
          _ = u * y * x := by rw [hku, hkx, hky]
          _ = u * x * y := by
              have hxy : x * y = y * x := hZ1abel x hxZ y hyZ
              calc u * y * x = u * (y * x) := by group
                _ = u * (x * y) := by rw [← hxy]
                _ = u * x * y := by group
    have h := congrArg (· * k) hkσ'
    simpa [mul_assoc] using h
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [hσ, hx, hy] using hkσ)

private theorem edgeSylow_one_le_centralizer_mul_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h2 : centerOf Y.S = Y.Z 0) (h4 : Y.Z 0 ≤ Y.Q 1) {a b : G}
    (ha : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2) (hb : b ∈ Y.L 1)
    (hb0 : b • Y.vert 0 ≠ Y.vert 0) (hb2 : b • Y.vert 0 ≠ Y.vert 2) {u : G}
    (hu : u ∈ Y.Z 0) :
    Y.edgeSylow 1 ≤ Subgroup.centralizer ({u * (a * u * a⁻¹) * (b * u * b⁻¹)} : Set G) := by
  have hE1leL1 : Y.edgeSylow 1 ≤ Y.L 1 := Y.edgeSylow_le_L 1
  have hEfix1 : Y.edgeSylow 1 ≤ MulAction.stabilizer G (Y.vert 1) :=
    (Y.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left
  have hEfix2 : Y.edgeSylow 1 ≤ MulAction.stabilizer G (Y.vert 2) :=
    (Y.isSylowTwoOf_edgeSylow 1).1.trans inf_le_right
  have hbadj : Γ.Adj (Y.vert 1) (b • Y.vert 0) := by
    have h := (Y.hyp.adj_smul b (Y.vert 1) (Y.vert 0)).mpr (adj_one_zero Y)
    rwa [MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 1 hb)] at h
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := Z_zero_le_Z_one Y H hZ h2 h4
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := Z_two_le_Z_one Y H hZ
  have hZa : conjSub a (Y.Z 0) = Y.Z 2 := by
    have h := vertZ_smul (G := G) a (Y.vert 0)
    rw [ha0] at h
    show conjSub a (vertZ (Y.vert 0)) = vertZ (Y.vert 2)
    exact h.symm
  have hZb1 : conjSub b (Y.Z 0) ≤ Y.Z 1 := by
    have h := Z_one_eq_iSup_conj Y H hZ h2 h4
    rw [← h]
    exact le_iSup₂_of_le b hb le_rfl
  have hZ1abel : ∀ p ∈ Y.Z 1, ∀ q ∈ Y.Z 1, p * q = q * p := Y.Z_commute 1
  have huZ : u ∈ Y.Z 1 := hZ0Z1 hu
  set x : G := a * u * a⁻¹ with hx
  set y : G := b * u * b⁻¹ with hy
  set σ : G := u * x * y with hσ
  have hxZ : x ∈ Y.Z 1 := by
    rw [hx]
    exact hZ2Z1 (hZa ▸ mul_mem_conjSub hu)
  have hyZ : y ∈ Y.Z 1 := by
    rw [hy]
    exact hZb1 (mul_mem_conjSub hu)
  intro k hk
  have hk2 : k • Y.vert 2 = Y.vert 2 := MulAction.mem_stabilizer_iff.mp (hEfix2 hk)
  have hk1 : k • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp (hEfix1 hk)
  have hk0v : Γ.Adj (Y.vert 1) (k • Y.vert 0) := by
    have h := (Y.hyp.adj_smul k (Y.vert 1) (Y.vert 0)).mpr (adj_one_zero Y)
    rwa [hk1] at h
  have hkx : k * x * k⁻¹ = x := by
    rw [hx]
    exact conj_conj_eq_of_smul_eq Y H hZ h2 (hE1leL1 hk) ha ha
      (by rw [mul_smul, ha0, hk2]) hu
  have hk0case : k • Y.vert 0 = Y.vert 0 ∨ k • Y.vert 0 = b • Y.vert 0 := by
    have hne2 : k • Y.vert 0 ≠ Y.vert 2 := by
      intro h
      exact (vert_zero_ne_vert_two Y)
        (MulAction.injective k (h.trans hk2.symm))
    by_cases h0 : k • Y.vert 0 = Y.vert 0
    · exact Or.inl h0
    · exact Or.inr (eq_of_adj_one_of_ne Y H hk0v hbadj h0 hne2 hb0 hb2)
  have hkσ : k * σ = σ * k := by
    have hkσ' : k * σ * k⁻¹ = σ := by
      rcases hk0case with h0' | h0'
      · have hku : k * u * k⁻¹ = u := by
          have hc := conj_eq_of_smul_eq Y H hZ h2 (hE1leL1 hk) (one_mem (Y.L 1))
            (by simpa using h0') hu
          simpa using hc
        have hyb : k * y * k⁻¹ = y := by
          have hkb0 : (k * b) • Y.vert 0 = b • Y.vert 0 := by
            rw [mul_smul]
            exact (smul_third_of_smul_zero Y H (Y.L_le_Gi 1 (hE1leL1 hk)) hbadj hb0 hb2
              hk2).1 h0'
          have hkb : k * b ∈ Y.L 1 := (Y.L 1).mul_mem (hE1leL1 hk) hb
          have hc := conj_eq_of_smul_eq Y H hZ h2 hkb hb hkb0 hu
          rw [hy]
          calc k * (b * u * b⁻¹) * k⁻¹ = (k * b) * u * (k * b)⁻¹ := by group
            _ = b * u * b⁻¹ := hc
        rw [hσ]
        calc k * (u * x * y) * k⁻¹ =
              (k * u * k⁻¹) * (k * x * k⁻¹) * (k * y * k⁻¹) := by group
          _ = u * x * y := by rw [hku, hkx, hyb]
      · have hku : k * u * k⁻¹ = y := by
          have hc := conj_eq_of_smul_eq Y H hZ h2 (hE1leL1 hk) hb h0' hu
          rw [hy]
          exact hc
        have hky : k * y * k⁻¹ = u := by
          have hkb0 : (k * b) • Y.vert 0 = Y.vert 0 := by
            rw [mul_smul]
            exact (smul_third_of_smul_zero Y H (Y.L_le_Gi 1 (hE1leL1 hk)) hbadj hb0 hb2
              hk2).2 h0'
          have hkb : k * b ∈ Y.L 1 := (Y.L 1).mul_mem (hE1leL1 hk) hb
          have hc := conj_eq_of_smul_eq Y H hZ h2 hkb (one_mem (Y.L 1))
            (by simpa using hkb0) hu
          rw [hy]
          calc k * (b * u * b⁻¹) * k⁻¹ = (k * b) * u * (k * b)⁻¹ := by group
            _ = 1 * u * 1⁻¹ := hc
            _ = u := by group
        rw [hσ]
        calc k * (u * x * y) * k⁻¹ =
              (k * u * k⁻¹) * (k * x * k⁻¹) * (k * y * k⁻¹) := by group
          _ = y * x * u := by rw [hku, hkx, hky]
          _ = u * x * y := by
              have hyx : y * x = x * y := hZ1abel y hyZ x hxZ
              have hux : u * x = x * u := hZ1abel u huZ x hxZ
              calc y * x * u = (y * x) * u := by group
                _ = (x * y) * u := by rw [hyx]
                _ = x * (y * u) := by group
                _ = x * (u * y) := by rw [hZ1abel y hyZ u huZ]
                _ = (x * u) * y := by group
                _ = (u * x) * y := by rw [hux]
                _ = u * x * y := by group
    have h := congrArg (· * k) hkσ'
    simpa [mul_assoc] using h
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [hσ, hx, hy] using hkσ)

private theorem conjSub_Z_zero_le_sup_of_not (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h2 : centerOf Y.S = Y.Z 0) (h3 : centerOf (Y.L 1) = ⊥)
    (h4 : Y.Z 0 ≤ Y.Q 1) {a b : G} (ha : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2)
    (hb : b ∈ Y.L 1) (hb0 : b • Y.vert 0 ≠ Y.vert 0) (hb2 : b • Y.vert 0 ≠ Y.vert 2) :
    conjSub b (Y.Z 0) ≤ Y.Z 0 ⊔ Y.Z 2 := by
  classical
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := Z_zero_le_Z_one Y H hZ h2 h4
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := Z_two_le_Z_one Y H hZ
  have hZ1L : Y.Z 1 ≤ Y.L 1 :=
    (Y.Z_le_Q 1).trans ((Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1))
  have hZa : conjSub a (Y.Z 0) = Y.Z 2 := by
    have h := vertZ_smul (G := G) a (Y.vert 0)
    rw [ha0] at h
    show conjSub a (vertZ (Y.vert 0)) = vertZ (Y.vert 2)
    exact h.symm
  have hZb1 : conjSub b (Y.Z 0) ≤ Y.Z 1 := by
    have h := Z_one_eq_iSup_conj Y H hZ h2 h4
    rw [← h]
    exact le_iSup₂_of_le b hb le_rfl
  have hJ : Y.L 1 = Y.S ⊔ Y.edgeSylow 1 := by
    rw [← Y.edgeSylow_zero]
    exact (Y.edgeSylow_sup_edgeSylow 1).symm
  have hmain : ∀ u ∈ Y.Z 0, u * (a * u * a⁻¹) * (b * u * b⁻¹) = 1 := by
    intro u hu
    set x : G := a * u * a⁻¹ with hx
    set y : G := b * u * b⁻¹ with hy
    set σ : G := u * x * y with hσ
    have huZ : u ∈ Y.Z 1 := hZ0Z1 hu
    have hxZ : x ∈ Y.Z 1 := by
      rw [hx]
      exact hZ2Z1 (hZa ▸ mul_mem_conjSub hu)
    have hyZ : y ∈ Y.Z 1 := by
      rw [hy]
      exact hZb1 (mul_mem_conjSub hu)
    have hZ1abel : ∀ p ∈ Y.Z 1, ∀ q ∈ Y.Z 1, p * q = q * p := Y.Z_commute 1
    have hσZ : σ ∈ Y.Z 1 := by
      rw [hσ]
      exact (Y.Z 1).mul_mem ((Y.Z 1).mul_mem huZ hxZ) hyZ
    have hScent : Y.S ≤ Subgroup.centralizer ({σ} : Set G) := by
      simpa [hσ, hx, hy] using
        S_le_centralizer_mul_conj Y H hZ h2 h4 ha ha0 hb hb0 hb2 hu
    have hEcent : Y.edgeSylow 1 ≤ Subgroup.centralizer ({σ} : Set G) := by
      simpa [hσ, hx, hy] using
        edgeSylow_one_le_centralizer_mul_conj Y H hZ h2 h4 ha ha0 hb hb0 hb2 hu
    have hσcenter : σ ∈ centerOf (Y.L 1) := by
      refine Subgroup.mem_inf.mpr ⟨hZ1L hσZ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : l ∈ Y.S ⊔ Y.edgeSylow 1 := by rwa [← hJ]
      exact Subgroup.mem_centralizer_singleton_iff.mp (sup_le hScent hEcent hl')
    have hσbot : σ = 1 := by
      have h := hσcenter
      rw [h3] at h
      simpa using h
    rw [hσ] at hσbot
    rw [hx, hy] at hσbot
    exact hσbot
  intro z hz
  set u : G := b⁻¹ * z * b with hu_def
  have hu : u ∈ Y.Z 0 := mem_conjSub.mp hz
  have hzEq : z = b * u * b⁻¹ := by rw [hu_def]; group
  have hprod : u * (a * u * a⁻¹) * (b * u * b⁻¹) = 1 := hmain u hu
  set p : G := u * (a * u * a⁻¹) with hp_def
  set q : G := b * u * b⁻¹ with hq_def
  have hpq : p * q = 1 := by rw [hp_def, hq_def]; exact hprod
  have hq : q = p⁻¹ := by
    calc q = p⁻¹ * p * q := by group
      _ = p⁻¹ * (p * q) := by group
      _ = p⁻¹ * 1 := by rw [hpq]
      _ = p⁻¹ := by group
  have hu' : u ∈ Y.Z 0 ⊔ Y.Z 2 := Subgroup.mem_sup_left hu
  have hxa : a * u * a⁻¹ ∈ Y.Z 0 ⊔ Y.Z 2 :=
    Subgroup.mem_sup_right (hZa ▸ mul_mem_conjSub hu)
  have hp_mem : p ∈ Y.Z 0 ⊔ Y.Z 2 := by
    rw [hp_def]
    exact Subgroup.mul_mem _ hu' hxa
  rw [hzEq, hq]
  exact Subgroup.inv_mem _ hp_mem

private theorem Z_one_eq_sup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) (h3 : centerOf (Y.L 1) = ⊥) (h4 : Y.Z 0 ≤ Y.Q 1) :
    Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := by
  classical
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := Z_zero_le_Z_one Y H hZ h2 h4
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := Z_two_le_Z_one Y H hZ
  refine le_antisymm ?_ (sup_le hZ0Z1 hZ2Z1)
  rw [← Z_one_eq_iSup_conj Y H hZ h2 h4]
  refine iSup_le fun g => iSup_le fun hg => ?_
  change conjSub g (Y.Z 0) ≤ Y.Z 0 ⊔ Y.Z 2
  obtain ⟨a, ha, ha0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) (Y.vert 2)
    ((SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) (Y.vert 0)).mpr (adj_one_zero Y))
    ((SimpleGraph.mem_neighborSet (G := Γ) (Y.vert 1) (Y.vert 2)).mpr (adj_one_two Y))
  have ha0' : a • Y.vert 0 = Y.vert 2 := ha0
  by_cases hg0 : g • Y.vert 0 = Y.vert 0
  · have hle : conjSub g (Y.Z 0) ≤ Y.Z 0 := by
      intro z hz
      have hu : g⁻¹ * z * g ∈ Y.Z 0 := mem_conjSub.mp hz
      have hc := conj_eq_of_smul_eq Y H hZ h2 hg (one_mem (Y.L 1))
        (by simpa using hg0) hu
      have hzEq : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [hzEq, hc]
      simpa using hu
    exact hle.trans (le_sup_left)
  · by_cases hg2 : g • Y.vert 0 = Y.vert 2
    · have hle : conjSub g (Y.Z 0) ≤ Y.Z 2 := by
        intro z hz
        have hu : g⁻¹ * z * g ∈ Y.Z 0 := mem_conjSub.mp hz
        have hc := conj_eq_of_smul_eq Y H hZ h2 hg ha (hg2.trans ha0'.symm) hu
        have hzEq : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        rw [hzEq, hc]
        have hZa : conjSub a (Y.Z 0) = Y.Z 2 := by
          have h := vertZ_smul (G := G) a (Y.vert 0)
          rw [ha0'] at h
          show conjSub a (vertZ (Y.vert 0)) = vertZ (Y.vert 2)
          exact h.symm
        exact hZa ▸ mul_mem_conjSub hu
      exact hle.trans le_sup_right
    · exact conjSub_Z_zero_le_sup_of_not Y H hZ h2 h3 h4 ha ha0' hg hg0 hg2

private theorem Z_zero_inf_Z_two_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h2 : centerOf Y.S = Y.Z 0) (h3 : centerOf (Y.L 1) = ⊥) (h4 : Y.Z 0 ≤ Y.Q 1) :
    Y.Z 0 ⊓ Y.Z 2 = ⊥ := by
  have hcenS : Y.Z 0 ⊓ Y.Z 2 ≤ Subgroup.centralizer (Y.S : Set G) :=
    inf_le_left.trans (h2 ▸ (inf_le_right : centerOf Y.S ≤
      Subgroup.centralizer (Y.S : Set G)))
  have hcenE : Y.Z 0 ⊓ Y.Z 2 ≤ Subgroup.centralizer (Y.edgeSylow 1 : Set G) :=
    inf_le_right.trans ((center_edgeSylow_one_eq_Z_two Y H hZ) ▸
      (inf_le_right : centerOf (Y.edgeSylow 1) ≤
        Subgroup.centralizer (Y.edgeSylow 1 : Set G)))
  have hL : Y.S ⊔ Y.edgeSylow 1 = Y.L 1 := by
    rw [← Y.edgeSylow_zero]
    exact Y.edgeSylow_sup_edgeSylow 1
  have hCL : Y.Z 0 ⊓ Y.Z 2 ≤ Subgroup.centralizer (Y.L 1 : Set G) := by
    rw [← hL]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hcenS hcenE
  have hZ1L : Y.Z 1 ≤ Y.L 1 :=
    (Y.Z_le_Q 1).trans ((Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1))
  have hZle : Y.Z 0 ⊓ Y.Z 2 ≤ Y.Z 1 :=
    inf_le_left.trans (Z_zero_le_Z_one Y H hZ h2 h4)
  have hle : Y.Z 0 ⊓ Y.Z 2 ≤ centerOf (Y.L 1) := by
    refine (le_inf hZle hCL).trans ?_
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hZ1L hx.1, hx.2⟩
  rw [h3] at hle
  exact le_bot_iff.mp hle

theorem s52_step8 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 0 = centerOf (Y.L 0) ∧ centerOf Y.S = Y.Z 0 ∧ centerOf (Y.L 1) = ⊥ ∧
      Y.Z 0 ≤ Y.Q 1 ∧ Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 ∧ Y.Z 0 ⊓ Y.Z 2 = ⊥ ∧
        Nat.card (Y.Z 0) = 2 ∧ Y.Zt 1 = ⊥ := by
  have h1 : Y.Z 0 = centerOf (Y.L 0) := Z_zero_eq_centerOf_L_zero_of_Zt Y H hZ
  have h2 : centerOf Y.S = Y.Z 0 := center_S_eq_Z_zero Y H hZ h1
  have h3 : centerOf (Y.L 1) = ⊥ := center_L_one_eq_bot Y H hZ h1 h2
  have h4 : Y.Z 0 ≤ Y.Q 1 := Z_zero_le_Q_one_of_center Y H hZ h1 h3
  have h5 : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := Z_one_eq_sup Y H hZ h2 h3 h4
  have h6 : Y.Z 0 ⊓ Y.Z 2 = ⊥ := Z_zero_inf_Z_two_eq_bot Y H hZ h2 h3 h4
  exact ⟨h1, h2, h3, h4, h5, h6, (card_Z_zero_and_Zt_one Y H hZ h2 h5 h6).1,
    (card_Z_zero_and_Zt_one Y H hZ h2 h5 h6).2⟩

theorem s52_step8_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) (i : ℤ) (hi : Odd i) :
    Y.Z i = Y.Z (i - 1) ⊔ Y.Z (i + 1) ∧ Y.Z (i - 1) ⊓ Y.Z (i + 1) = ⊥ := by
  obtain ⟨m, hm⟩ := hi
  obtain ⟨-, -, -, -, hsup, hinf, -, -⟩ := Y.s52_step8 H hZ
  have h1 : Y.Z i = conjSub (Y.τ ^ m) (Y.Z 1) := by
    rw [show i = 1 + 2 * m by omega, Y.Z_add]
  have hA : Y.Z (i - 1) = conjSub (Y.τ ^ m) (Y.Z 0) := by
    rw [show i - 1 = 0 + 2 * m by omega, Y.Z_add]
  have hB : Y.Z (i + 1) = conjSub (Y.τ ^ m) (Y.Z 2) := by
    rw [show i + 1 = 2 + 2 * m by omega, Y.Z_add]
  refine ⟨?_, ?_⟩
  · rw [h1, hsup, conjSub_sup, ← hA, ← hB]
  · rw [hA, hB, ← conjSub_inf, hinf, conjSub_bot]

private theorem hasB_iff_of_even (Y : Setup Γ G) {i j : ℤ} (hij : Even (i - j)) (d : ℕ) :
    Y.HasB i d ↔ Y.HasB j d := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, i - j = 2 * m := by
    obtain ⟨k, hk⟩ := hij
    exact ⟨k, by omega⟩
  have hZ : Y.Z i = conjSub (Y.τ ^ m) (Y.Z j) := by
    rw [show i = j + 2 * m by omega, Y.Z_add]
  have hGi : ∀ k : ℤ, Y.Gi (i + k) = conjSub (Y.τ ^ m) (Y.Gi (j + k)) := by
    intro k
    rw [show i + k = (j + k) + 2 * m by omega, Y.Gi_add]
  have hiff : ∀ {A B : Subgroup G}, A ≤ B ↔ conjSub (Y.τ ^ m) A ≤ conjSub (Y.τ ^ m) B :=
    fun {_ _} => (Subgroup.map_le_map_iff_of_injective (MulAut.conj _).injective).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k] at h
      exact hiff.mpr h
    · intro h
      refine h2 ?_
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, Y.Gi_add]
      exact hiff.mp h
    · intro h
      refine h3 ?_
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, Y.Gi_add]
      exact hiff.mp h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have h := h1 k hk
      rw [hZ, hGi k]
      exact hiff.mp h
    · intro h
      refine h2 ?_
      rw [hZ, show i + (d : ℤ) + 1 = (j + (d : ℤ) + 1) + 2 * m by omega, Y.Gi_add] at h
      exact hiff.mpr h
    · intro h
      refine h3 ?_
      rw [hZ, show i - (d : ℤ) - 1 = (j - (d : ℤ) - 1) + 2 * m by omega, Y.Gi_add] at h
      exact hiff.mpr h

theorem s52_step8_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) (i : ℤ) (hi : Odd i) :
    IsElemAbelian 2 (Y.Z i) ∧ Nat.card (Y.Z i) = 4 := by
  obtain ⟨hsup, hinf⟩ := Y.s52_step8_odd H hZ i hi
  obtain ⟨-, -, -, -, -, -, hcard0, -⟩ := Y.s52_step8 H hZ
  obtain ⟨m, hm⟩ := hi
  have hcard2 : Nat.card (Y.Z 2) = 2 := by
    rw [show (2 : ℤ) = 0 + 2 * 1 by norm_num, Y.Z_add, card_conjSub, hcard0]
  have hcardA : Nat.card (Y.Z (i - 1)) = 2 := by
    rw [show i - 1 = 0 + 2 * m by omega, Y.Z_add, card_conjSub, hcard0]
  have hcardB : Nat.card (Y.Z (i + 1)) = 2 := by
    rw [show i + 1 = 2 + 2 * m by omega, Y.Z_add, card_conjSub, hcard2]
  have hcomm : ∀ a ∈ Y.Z (i - 1), ∀ b ∈ Y.Z (i + 1), a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ Y.Z i := by rw [hsup]; exact Subgroup.mem_sup_left ha
    have hb' : b ∈ Y.Z i := by rw [hsup]; exact Subgroup.mem_sup_right hb
    exact Y.Z_commute i a ha' b hb'
  have hnorm : Y.Z (i + 1) ≤ Subgroup.normalizer (Y.Z (i - 1) : Set G) := by
    refine (show Y.Z (i + 1) ≤ Subgroup.centralizer (Y.Z (i - 1) : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hdisj : Disjoint (Y.Z (i - 1)) (Y.Z (i + 1)) := disjoint_iff.mpr hinf
  have hcard : Nat.card (Y.Z i) = 4 := by
    rw [hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      hcardA, hcardB]
  refine ⟨?_, hcard⟩
  rw [hsup]
  exact CFSG.Open.IsElemAbelian.sup_of_commute
    (isElemAbelian_of_card_eq_two hcardA) (isElemAbelian_of_card_eq_two hcardB) hcomm

theorem hasB_iff (Y : Setup Γ G) (i : ℤ) (d : ℕ) :
    Y.HasB i d ↔ ∀ j : ℤ, (Y.Z i ≤ Y.Gi (i + j) ↔ j.natAbs ≤ d) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ j
    refine ⟨?_, h1 j⟩
    intro hj
    by_contra hle
    rw [not_le] at hle
    have hsplit : (d : ℤ) < j ∨ j < -(d : ℤ) := by omega
    rcases hsplit with hgt | hlt
    · exact h2 (fun z hz =>
        Y.mem_Gi_of_between (Y.Z_le_Gi i hz) (hj hz) (by omega) (by omega))
    · exact h3 (fun z hz =>
        Y.mem_Gi_of_between (hj hz) (Y.Z_le_Gi i hz) (by omega) (by omega))
  · intro h
    refine ⟨fun j hj => (h j).mpr hj, ?_, ?_⟩
    · intro hle
      have h0 : Y.Z i ≤ Y.Gi (i + ((d : ℤ) + 1)) := by
        rw [show i + ((d : ℤ) + 1) = i + (d : ℤ) + 1 by ring]
        exact hle
      have h1 : ((d : ℤ) + 1).natAbs ≤ d := (h ((d : ℤ) + 1)).mp h0
      omega
    · intro hle
      have h1 : (-(d : ℤ) - 1).natAbs ≤ d := (h (-(d : ℤ) - 1)).mp (by
        rw [show i - (d : ℤ) - 1 = i + (-(d : ℤ) - 1) by ring] at hle
        exact hle)
      omega

private theorem exists_hasB (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : Y.Zt i = ⊥) : ∃ d : ℕ, Y.HasB i d := by
  classical
  have hfix_iff : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ Y.Z i ≤ Y.Gi k := by
    intro k
    constructor
    · intro h z hz
      exact MulAction.mem_stabilizer_iff.mpr (h z hz)
    · intro h z hz
      exact MulAction.mem_stabilizer_iff.mp (h hz)
  have hi_mem : i ∈ Y.fixSet (Y.Z i) :=
    (hfix_iff i).mpr ((Y.Z_le_Q i).trans (Y.Q_le_Gi i))
  have hsym : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ (2 * i - k) ∈ Y.fixSet (Y.Z i) := by
    intro k
    rw [hfix_iff k, hfix_iff (2 * i - k)]
    have h := Y.Z_fix_symm H i hK (k - i)
    rwa [show i + (k - i) = k by ring, show i - (k - i) = 2 * i - k by ring] at h
  have hnotuniv : Y.fixSet (Y.Z i) ≠ Set.univ := by
    intro huniv
    have hle : Y.Z i ≤ Y.GT ⊓ Y.Z i := le_inf (Y.le_GT_of_fixSet_eq_univ huniv) le_rfl
    rw [inf_eq_bot_of_odd_of_isPGroup H.odd_GT
      ((pCoreOf_isPGroup' (Y.Gi i)).to_le (Y.Z_le_Q i))] at hle
    exact Y.Z_ne_bot_of i (Y.Q_ne_bot H.char i) (le_bot_iff.mp hle)
  have htrich := fixSet_trichotomy Y.hyp.isTree Y.hyp.adj_smul Y.hyp.finite_stab Y.toTrack
    (Y.Z i)
  rcases htrich with huniv | hempty | ⟨a, b, hab, hI⟩
  · exact absurd huniv hnotuniv
  · rw [Set.eq_empty_iff_forall_notMem] at hempty
    exact absurd (hempty i hi_mem) (by simp)
  have hmemI : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ a ≤ k ∧ k ≤ b := by
    intro k
    rw [hI]
    exact Set.mem_Icc
  have hai : a ≤ i := ((hmemI i).mp hi_mem).1
  have hib : i ≤ b := ((hmemI i).mp hi_mem).2
  have habsum : a + b = 2 * i := by
    have ha_mem : a ∈ Y.fixSet (Y.Z i) := (hmemI a).mpr ⟨le_rfl, hab⟩
    have hb_mem : b ∈ Y.fixSet (Y.Z i) := (hmemI b).mpr ⟨hab, le_rfl⟩
    have h1 : 2 * i - a ≤ b := ((hmemI _).mp ((hsym a).mp ha_mem)).2
    have h2 : a ≤ 2 * i - b := ((hmemI _).mp ((hsym b).mp hb_mem)).1
    omega
  refine ⟨(b - i).toNat, ?_⟩
  have hbi : 0 ≤ b - i := by omega
  have hdcast : (((b - i).toNat : ℕ) : ℤ) = b - i := Int.toNat_of_nonneg hbi
  have haeq : a = i - (b - i) := by omega
  have hbeq : b = i + (b - i) := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj' : -(b - i) ≤ j ∧ j ≤ b - i := by
      have h1 : (j.natAbs : ℤ) ≤ ((b - i).toNat : ℤ) := by exact_mod_cast hj
      rw [hdcast] at h1
      constructor
      · rcases Int.natAbs_eq j with h | h <;> rw [h] at h1 <;> omega
      · rcases Int.natAbs_eq j with h | h <;> rw [h] at h1 <;> omega
    have hmem : i + j ∈ Y.fixSet (Y.Z i) := by
      rw [hmemI]
      constructor <;> omega
    exact (hfix_iff (i + j)).mp hmem
  · intro hle
    have hmem : i + ((b - i).toNat : ℤ) + 1 ∈ Y.fixSet (Y.Z i) :=
      (hfix_iff _).mpr hle
    have hbound := ((hmemI _).mp hmem).2
    omega
  · intro hle
    have hmem : i - ((b - i).toNat : ℤ) - 1 ∈ Y.fixSet (Y.Z i) :=
      (hfix_iff _).mpr hle
    have hbound := ((hmemI _).mp hmem).1
    omega

private theorem hasB_one_eq_pred_of_hasB_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d0 d1 : ℕ} (h0 : Y.HasB 0 d0) (h1 : Y.HasB 1 d1) :
    1 ≤ d0 ∧ d1 = d0 - 1 ∧ Odd d0 := by
  have h8 := Y.s52_step8 H hZ
  obtain ⟨-, -, -, h4, h5, -, -, -⟩ := h8
  have h0i := (Y.hasB_iff 0 d0).mp h0
  have h1i := (Y.hasB_iff 1 d1).mp h1
  have h2HasB : Y.HasB 2 d0 :=
    (Y.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) d0).mpr h0
  have h2i := (Y.hasB_iff 2 d0).mp h2HasB
  have hkey : ∀ k : ℤ, (k - 1).natAbs ≤ d1 ↔ k.natAbs ≤ d0 ∧ (k - 2).natAbs ≤ d0 := by
    intro k
    have h1k : Y.Z 1 ≤ Y.Gi k ↔ (k - 1).natAbs ≤ d1 := by
      have h := h1i (k - 1)
      rwa [show 1 + (k - 1) = k by ring] at h
    have h0k : Y.Z 0 ≤ Y.Gi k ↔ k.natAbs ≤ d0 := by
      simpa using h0i k
    have h2k : Y.Z 2 ≤ Y.Gi k ↔ (k - 2).natAbs ≤ d0 := by
      have h := h2i (k - 2)
      rwa [show 2 + (k - 2) = k by ring] at h
    rw [← h1k, ← h0k, ← h2k]
    constructor
    · intro h
      rw [h5] at h
      exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩
    · rintro ⟨h0', h2'⟩
      rw [h5]
      exact sup_le h0' h2'
  have hd0ge : 1 ≤ d0 := by
    have h : Y.Z 0 ≤ Y.Gi (0 + (1 : ℤ)) := by
      simpa using h4.trans (Y.Q_le_Gi 1)
    have := (h0i 1).mp h
    simpa using this
  have hupper : d1 ≤ d0 - 1 := by
    have hL : (((d1 : ℤ) + 1 - 1).natAbs ≤ d1) := by
      have : (d1 : ℤ) + 1 - 1 = (d1 : ℤ) := by ring
      rw [this, Int.natAbs_cast]
    have hR := (hkey ((d1 : ℤ) + 1)).mp hL
    have hplus : (((d1 : ℤ) + 1).natAbs) = d1 + 1 := by
      rw [show (d1 : ℤ) + 1 = ((d1 + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_cast]
    rw [hplus] at hR
    have hcast : (d1 + 1 : ℤ) ≤ (d0 : ℤ) := by exact_mod_cast hR.1
    omega
  have hlower : d0 - 1 ≤ d1 := by
    have hR : ((d0 : ℤ).natAbs ≤ d0 ∧ ((d0 : ℤ) - 2).natAbs ≤ d0) := by
      refine ⟨by rw [Int.natAbs_cast], ?_⟩
      have h1 : ((((d0 : ℤ) - 2).natAbs : ℤ)) ≤ (d0 : ℤ) := by
        rcases Int.natAbs_eq ((d0 : ℤ) - 2) with h | h
        · rw [h]; omega
        · rw [h]; omega
      exact_mod_cast h1
    have hL := (hkey (d0 : ℤ)).mpr hR
    have hcast : (((d0 : ℤ) - 1).natAbs) = d0 - 1 := by
      rw [show (d0 : ℤ) - 1 = ((d0 - 1 : ℕ) : ℤ) by push_cast [hd0ge]; ring,
        Int.natAbs_cast]
    rw [hcast] at hL
    exact hL
  have hodd : Odd d0 := by
    rcases Int.even_or_odd (d0 : ℤ) with he | ho
    · exfalso
      have hZ0d : Y.Z 0 ≤ Y.Gi (0 + (d0 : ℤ)) := (h0i (d0 : ℤ)).mpr (by rw [Int.natAbs_cast])
      have hZ0p : IsPGroup 2 (Y.Z 0) :=
        (pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0)
      have hZ0d' : Y.Z 0 ≤ Y.Gi (d0 : ℤ) := by simpa using hZ0d
      have hQ : Y.Z 0 ≤ Y.Q (d0 : ℤ) :=
        le_Q_of_comm_K_eq_bot Y H he hZ0d' hZ0p hZ
      have hfixn : Y.Z 0 ≤ Y.Gi ((d0 : ℤ) + 1) := by
        intro z hz
        exact MulAction.mem_stabilizer_iff.mp
          (Y.Q_fixes_neighbors_vert (d0 : ℤ) (Y.vert ((d0 : ℤ) + 1))
            (by simpa using Y.adj (d0 : ℤ)) z (hQ hz))
      exact h0.2.1 (by simpa using hfixn)
    · obtain ⟨k, hk⟩ := ho
      have hk0 : 0 ≤ k := by omega
      refine ⟨k.toNat, ?_⟩
      have hkk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
      omega
  exact ⟨hd0ge, by omega, hodd⟩

private theorem commutator_mem_of_relIndex_two_of_centralizes {A B : Subgroup G}
    (h : A.relIndex B = 2) {x : G} (hxB : conjSub x B = B)
    (hxA : x ∈ Subgroup.centralizer (A : Set G)) {y : G} (hy : y ∈ B) :
    ⁅x, y⁆ ∈ A := by
  have hconjB : x * y * x⁻¹ ∈ B := by
    have hc := mul_mem_conjSub (H := B) (g := x) hy
    rwa [hxB] at hc
  have hinvB : y⁻¹ ∈ B := B.inv_mem hy
  have hiff : ((⟨x * y * x⁻¹, hconjB⟩ : B) ∈ A.subgroupOf B ↔
      (⟨y⁻¹, hinvB⟩ : B) ∈ A.subgroupOf B) := by
    have hxinv : x⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.centralizer (A : Set G)).inv_mem hxA
    constructor
    · intro hmem
      have hmemA : x * y * x⁻¹ ∈ A := Subgroup.mem_subgroupOf.mp hmem
      have hz := Subgroup.mem_centralizer_iff.mp hxinv (x * y * x⁻¹) hmemA
      have hyA : y ∈ A := by
        rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group,
          show x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ by rw [← hz]; group]
        exact hmemA
      exact A.inv_mem_iff.mpr hyA
    · intro hmem
      have hyA : y ∈ A := A.inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
      have hc := Subgroup.mem_centralizer_iff.mp hxA y hyA
      refine Subgroup.mem_subgroupOf.mpr ?_
      change x * y * x⁻¹ ∈ A
      rw [show x * y * x⁻¹ = y by rw [← hc]; group]
      exact hyA
  have hmem := Subgroup.mem_subgroupOf.mp
    ((Subgroup.mul_mem_iff_of_index_two (H := A.subgroupOf B) h
      (a := (⟨x * y * x⁻¹, hconjB⟩ : B)) (b := (⟨y⁻¹, hinvB⟩ : B))).mpr hiff)
  simpa [commutatorElement_def] using hmem

private theorem le_sup_zpowers_of_relIndex_eq_two {A B : Subgroup G} {x : G} (hAB : A ≤ B)
    (hx : x ∈ B) (hxA : x ∉ A) (h : A.relIndex B = 2) : B ≤ A ⊔ Subgroup.zpowers x := by
  have hS_e1 : A ⊔ Subgroup.zpowers x ≤ B := sup_le hAB (Subgroup.zpowers_le.mpr hx)
  have hSne : A ⊔ Subgroup.zpowers x ≠ A := by
    intro hEq
    exact hxA (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hrel_ne : A.relIndex (A ⊔ Subgroup.zpowers x) ≠ 1 := by
    intro h1
    exact hSne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) le_sup_left)
  have hrel_dvd : A.relIndex (A ⊔ Subgroup.zpowers x) ∣ 2 := by
    have hm := Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ Subgroup.zpowers x)
      (L := B) le_sup_left hS_e1
    rw [h] at hm
    exact ⟨_, hm.symm⟩
  have hrel_eq : A.relIndex (A ⊔ Subgroup.zpowers x) = 2 := by
    rcases Nat.dvd_prime (by norm_num : Nat.Prime 2) |>.mp hrel_dvd with h1 | h1
    · exact absurd h1 hrel_ne
    · exact h1
  refine Subgroup.relIndex_eq_one.mp ?_
  have hm := Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ Subgroup.zpowers x)
    (L := B) le_sup_left hS_e1
  rw [hrel_eq, h] at hm
  omega

private theorem commutator_Z_one_Z_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {j : ℤ} (hj : Odd j) (hZ1j : Y.Z 1 ≤ Y.Gi j)
    (hZ1j' : Y.Z 1 ≤ Y.Gi (j - 1)) (hZ1j1 : ¬ Y.Z 1 ≤ Y.Gi (j + 1)) :
    ⁅Y.Z 1, Y.Z j⁆ ≠ ⊥ := by
  classical
  obtain ⟨m, hm⟩ := hj
  have hD : j = 1 + 2 * (m : ℤ) := by omega
  have h3c : centerOf (Y.L 1) = ⊥ := (Y.s52_step8 H hZ).2.2.1
  intro hRbot
  have hZ1C : Y.Z 1 ≤ Subgroup.centralizer (Y.Z j : Set G) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hRbot
    exact hRbot
  set C : Subgroup G := Subgroup.centralizer (Y.Z j : Set G) with hC
  have hCN : ∀ g ∈ Y.Gi j, conjSub g C = C := by
    intro g hg
    rw [hC, ← conjSub_centralizer g (Y.Z j), Y.Z_normal j g hg]
  have hxexists : ∃ x ∈ Y.Z 1, x ∉ Y.Q j := by
    by_contra h
    push Not at h
    have hZ1Gj1 : Y.Z 1 ≤ Y.Gi (j + 1) := by
      intro x hx
      exact MulAction.mem_stabilizer_iff.mp
        (Y.Q_fixes_neighbors_vert j (Y.vert (j + 1))
          (by simpa using Y.adj j) x (h x hx))
    exact hZ1j1 hZ1Gj1
  obtain ⟨x, hxZ1, hxQ⟩ := hxexists
  have hxe1 : x ∈ Y.edgeSylow (j - 1) :=
    Y.le_edgeSylow_of_le_inf (U := Y.Z 1) (j - 1)
      ((pCoreOf_isPGroup' (Y.Gi 1)).to_le (Y.Z_le_Q 1))
      (le_inf hZ1j' (by simpa using hZ1j)) hxZ1
  have hQDe1 : Y.Q j ≤ Y.edgeSylow (j - 1) := by
    have h := Y.Q_le_edgeSylow_right j
    show Y.Q j ≤ pCoreOf 2 (Y.Gi (j - 1) ⊓ Y.Gi (j - 1 + 1))
    simpa [show j - 1 + 1 = j by ring] using h
  have hIdx : (Y.Q j).relIndex (Y.edgeSylow (j - 1)) = 2 := by
    have h := Y.relIndex_Q_succ_edgeSylow (j - 1)
    rw [show j - 1 + 1 = j by ring] at h
    have hn : Y.n j = 1 := by
      rw [hD, Y.n_add, H.n_one]
    rw [hn] at h
    simpa using h
  have he1_le : Y.edgeSylow (j - 1) ≤ Y.Q j ⊔ Subgroup.zpowers x :=
    le_sup_zpowers_of_relIndex_eq_two hQDe1 hxe1 hxQ hIdx
  have hQDC : Y.Q j ≤ C := by
    rw [Subgroup.le_centralizer_iff]
    exact (Y.Z_le_center j).trans inf_le_right
  have hxC : x ∈ C := hZ1C hxZ1
  have he1C : Y.edgeSylow (j - 1) ≤ C :=
    he1_le.trans (sup_le hQDC (Subgroup.zpowers_le.mpr hxC))
  haveI : Finite ↥(Y.L j) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi j)
  have hE1syl : IsSylowTwoOf (Y.edgeSylow (j - 1)) (Y.L j) := by
    have h := Y.isSylowTwoOf_edgeSylow_L_succ (j - 1)
    rwa [show j - 1 + 1 = j by ring] at h
  have hE2syl : IsSylowTwoOf (Y.edgeSylow j) (Y.L j) :=
    Y.isSylowTwoOf_edgeSylow_L j
  obtain ⟨g, hgL, hgE⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf hE1syl hE2syl
  have hgGi : g ∈ Y.Gi j := Y.L_le_Gi j hgL
  have he2C : Y.edgeSylow j ≤ C := by
    rw [hgE]
    calc conjSub g (Y.edgeSylow (j - 1)) ≤ conjSub g C := conjSub_mono g he1C
      _ = C := hCN g hgGi
  have hLC : Y.L j ≤ C := by
    rw [show Y.L j =
      Y.edgeSylow (j - 1) ⊔ Y.edgeSylow j from (Y.edgeSylow_sup_edgeSylow j).symm]
    exact sup_le he1C he2C
  have hZj_center : Y.Z j ≤ centerOf (Y.L j) := by
    have hZL : Y.Z j ≤ Y.L j :=
      (Y.Z_le_Q j).trans ((Y.Q_le_edgeSylow_left j).trans (Y.edgeSylow_le_L j))
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hZL hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlc : l ∈ C := hLC hl
    exact ((Subgroup.mem_centralizer_iff.mp hlc) z hz).symm
  have hcenterj : centerOf (Y.L j) = ⊥ := by
    have h := Y.L_add (m : ℤ) 1
    rw [← hD] at h
    rw [h, centerOf_conjSub, h3c, conjSub_bot]
  rw [hcenterj] at hZj_center
  exact Y.Z_ne_bot_of j (Y.Q_ne_bot H.char j) (le_bot_iff.mp hZj_center)

private theorem Z_pred_eq_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {j : ℤ} (hj : Odd j) (hZ1j : Y.Z 1 ≤ Y.Gi j)
    (hZ1j' : Y.Z 1 ≤ Y.Gi (j - 1)) (hZj1 : Y.Z j ≤ Y.Gi 1) (hZj2 : Y.Z j ≤ Y.Gi 2)
    (hR : ⁅Y.Z 1, Y.Z j⁆ ≠ ⊥) : Y.Z (j - 1) = Y.Z 2 := by
  classical
  obtain ⟨-, -, -, -, -, -, hcard0, -⟩ := Y.s52_step8 H hZ
  obtain ⟨m, hm⟩ := hj
  have hD : j = 1 + 2 * (m : ℤ) := by omega
  have hDodd : Odd j := ⟨m, by rw [hD]; ring⟩
  have hcardZD : Nat.card (Y.Z j) = 4 := (Y.s52_step8_Z H hZ j hDodd).2
  have hcardZDm1 : Nat.card (Y.Z (j - 1)) = 2 := by
    rw [show j - 1 = 0 + 2 * (m : ℤ) by omega, Y.Z_add, card_conjSub]
    exact hcard0
  have h5D : Y.Z j = Y.Z (j - 1) ⊔ Y.Z (j + 1) := (Y.s52_step8_odd H hZ j hDodd).1
  have hZ2card : Nat.card (Y.Z 2) = 2 := by
    rw [show (2 : ℤ) = 0 + 2 * (1 : ℤ) by norm_num, Y.Z_add, card_conjSub]
    exact hcard0
  have hcardZ1 : Nat.card (Y.Z 1) = 4 := (Y.s52_step8_Z H hZ 1 (by norm_num)).2
  have hR_leD : ⁅Y.Z 1, Y.Z j⁆ ≤ Y.Z j := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hxGD : x ∈ Y.Gi j := hZ1j hx
    have hconj : x * y * x⁻¹ ∈ Y.Z j := by
      have h := mul_mem_conjSub (H := Y.Z j) (g := x) hy
      rwa [Y.Z_normal j x hxGD] at h
    have h : (x * y * x⁻¹) * y⁻¹ ∈ Y.Z j :=
      (Y.Z j).mul_mem hconj ((Y.Z j).inv_mem hy)
    rwa [show x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ by group] at h
  have hrelD : (Y.Z (j - 1)).relIndex (Y.Z j) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Y.Z (j - 1)) (K := Y.Z j)
    rw [inf_eq_left.mpr (by rw [h5D]; exact le_sup_left), hcardZDm1, hcardZD] at h
    omega
  have hRZD : ⁅Y.Z 1, Y.Z j⁆ ≤ Y.Z (j - 1) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    exact commutator_mem_of_relIndex_two_of_centralizes hrelD
      (Y.Z_normal j x (hZ1j hx))
      (normalizer_le_centralizer_of_card_two hcardZDm1
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          (Y.Z_normal (j - 1) x (hZ1j' hx)))) hy
  have hrel1 : (Y.Z 2).relIndex (Y.Z 1) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Y.Z 2) (K := Y.Z 1)
    rw [inf_eq_left.mpr (Z_two_le_Z_one Y H hZ), hZ2card, hcardZ1] at h
    omega
  have hRZ2 : ⁅Y.Z 1, Y.Z j⁆ ≤ Y.Z 2 := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have h2' : ⁅y, x⁆ ∈ Y.Z 2 :=
      commutator_mem_of_relIndex_two_of_centralizes hrel1
        (Y.Z_normal 1 y (hZj1 hy))
        (normalizer_le_centralizer_of_card_two hZ2card
          (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Y.Z_normal 2 y (hZj2 hy)))) hx
    rw [show ⁅x, y⁆ = ⁅y, x⁆⁻¹ from (commutatorElement_inv y x).symm]
    exact (Y.Z 2).inv_mem h2'
  have hcardR : Nat.card ↥(⁅Y.Z 1, Y.Z j⁆) = 2 := by
    haveI : Finite ↥(Y.Gi j) := Y.hyp.finite_stab (Y.vert j)
    haveI : Finite ↥(⁅Y.Z 1, Y.Z j⁆) :=
      Finite.of_injective (Subgroup.inclusion (hR_leD.trans (Y.Z_le_Gi j)))
        (Subgroup.inclusion_injective _)
    have hdvd : Nat.card ↥(⁅Y.Z 1, Y.Z j⁆) ∣ 2 := by
      have h := Subgroup.relIndex_mul_card (H := ⁅Y.Z 1, Y.Z j⁆) (K := Y.Z (j - 1))
      rw [inf_eq_left.mpr hRZD, hcardZDm1] at h
      exact ⟨(⁅Y.Z 1, Y.Z j⁆).relIndex (Y.Z (j - 1)), by rw [mul_comm]; exact h.symm⟩
    have hne1 : Nat.card ↥(⁅Y.Z 1, Y.Z j⁆) ≠ 1 := by
      intro h
      exact hR (Subgroup.card_eq_one.mp h)
    rcases Nat.dvd_prime (by norm_num : Nat.Prime 2) |>.mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  haveI hfinDm1 : Finite ↥(Y.Z (j - 1)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert (j - 1))
      ((Y.Z_le_Q (j - 1)).trans (Y.Q_le_Gi (j - 1)))
  haveI hfinZ2 : Finite ↥(Y.Z 2) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 2)
      ((Y.Z_le_Q 2).trans (Y.Q_le_Gi 2))
  have hRD : ⁅Y.Z 1, Y.Z j⁆ = Y.Z (j - 1) :=
    Subgroup.eq_of_le_of_card_ge hRZD (by rw [hcardR, hcardZDm1])
  have hR2 : ⁅Y.Z 1, Y.Z j⁆ = Y.Z 2 :=
    Subgroup.eq_of_le_of_card_ge hRZ2 (by rw [hcardR, hZ2card])
  exact hRD.symm.trans hR2

private theorem eq_zero_of_conjSub_zpow_Z_two (Y : Setup Γ G) {d : ℕ}
    (h2 : ∀ j : ℤ, Y.Z 2 ≤ Y.Gi (2 + j) ↔ j.natAbs ≤ d) {k : ℤ}
    (hk : conjSub (Y.τ ^ k) (Y.Z 2) = Y.Z 2) : k = 0 := by
  by_contra hk0
  have hright : Y.Z 2 ≤ Y.Gi (2 + (d : ℤ) + 2 * k) := by
    have h2end : Y.Z 2 ≤ Y.Gi (2 + (d : ℤ)) := (h2 (d : ℤ)).mpr (by rw [Int.natAbs_cast])
    have h := conjSub_mono (Y.τ ^ k) h2end
    rw [hk, ← Y.Gi_add k (2 + (d : ℤ))] at h
    exact h
  have hleft : Y.Z 2 ≤ Y.Gi (2 - (d : ℤ) + 2 * k) := by
    have h2end : Y.Z 2 ≤ Y.Gi (2 - (d : ℤ)) :=
      (h2 (-(d : ℤ))).mpr (by rw [Int.natAbs_neg, Int.natAbs_cast])
    have h := conjSub_mono (Y.τ ^ k) h2end
    rw [hk, ← Y.Gi_add k (2 - (d : ℤ))] at h
    exact h
  have hr := (h2 ((d : ℤ) + 2 * k)).mp (by
    simpa only [add_assoc] using hright)
  have hl := (h2 (-(d : ℤ) + 2 * k)).mp (by
    simpa [sub_eq_add_neg, add_assoc] using hleft)
  have hr' : (((d : ℤ) + 2 * k).natAbs : ℤ) ≤ (d : ℤ) := by exact_mod_cast hr
  have hl' : ((-(d : ℤ) + 2 * k).natAbs : ℤ) ≤ (d : ℤ) := by exact_mod_cast hl
  have h1 : (d : ℤ) + 2 * k ≤ (d : ℤ) :=
    le_trans (Int.le_natAbs (a := (d : ℤ) + 2 * k)) hr'
  have hge : 0 ≤ 2 * k := by
    have hz : -(-(d : ℤ) + 2 * k) ≤ (d : ℤ) := by
      have h := Int.le_natAbs (a := -(-(d : ℤ) + 2 * k))
      rw [Int.natAbs_neg] at h
      exact le_trans h hl'
    omega
  omega

private theorem d0_eq_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d0 d1 : ℕ} (h0 : Y.HasB 0 d0) (h1 : Y.HasB 1 d1)
    (hd0ge : 1 ≤ d0) (hd1eq : d1 = d0 - 1) (hd0odd : Odd d0) : d0 = 3 := by
  classical
  obtain ⟨-, -, -, h4c, -, -, -, -⟩ := Y.s52_step8 H hZ
  have h0i := (Y.hasB_iff 0 d0).mp h0
  have h1i := (Y.hasB_iff 1 d1).mp h1
  have h2HasB : Y.HasB 2 d0 :=
    (Y.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) d0).mpr h0
  have h2i := (Y.hasB_iff 2 d0).mp h2HasB
  obtain ⟨m, hm⟩ := hd0odd
  have hD : (d0 : ℤ) = 1 + 2 * (m : ℤ) := by omega
  have hDodd : Odd (d0 : ℤ) := ⟨(m : ℤ), by rw [hD]; ring⟩
  have hHasBD : Y.HasB (d0 : ℤ) d1 := by
    refine (Y.hasB_iff_of_even (i := (d0 : ℤ)) (j := 1) ?_ d1).mpr h1
    exact ⟨(m : ℤ), by rw [hD]; ring⟩
  have hDi := (Y.hasB_iff (d0 : ℤ) d1).mp hHasBD
  have hd0ge2 : 2 ≤ d0 := by
    have hZ0G2 : Y.Z 0 ≤ Y.Gi 2 := by
      have h := Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (Y.adj 1)
      intro z hz
      exact MulAction.mem_stabilizer_iff.mpr (h z (h4c hz))
    have h := (h0i 2).mp hZ0G2
    simpa using h
  have hZD1 : Y.Z (d0 : ℤ) ≤ Y.Gi 1 := by
    have h := (hDi (1 - (d0 : ℤ))).mpr ?_
    · rwa [show (d0 : ℤ) + (1 - (d0 : ℤ)) = 1 by ring] at h
    · rw [hd1eq]
      rw [show (1 - (d0 : ℤ)) = -(((d0 - 1 : ℕ)) : ℤ) by push_cast [hd0ge]; ring,
        Int.natAbs_neg, Int.natAbs_cast]
  have hZD2 : Y.Z (d0 : ℤ) ≤ Y.Gi 2 := by
    have h := (hDi (2 - (d0 : ℤ))).mpr ?_
    · rwa [show (d0 : ℤ) + (2 - (d0 : ℤ)) = 2 by ring] at h
    · rw [hd1eq]
      rw [show (2 - (d0 : ℤ)) = -(((d0 - 2 : ℕ)) : ℤ) by push_cast [hd0ge2]; ring,
        Int.natAbs_neg, Int.natAbs_cast]
      omega
  have hZ1GD : Y.Z 1 ≤ Y.Gi (d0 : ℤ) := by
    have h := (h1i ((d0 : ℤ) - 1)).mpr ?_
    · rwa [show 1 + ((d0 : ℤ) - 1) = (d0 : ℤ) by ring] at h
    · rw [hd1eq]
      rw [show (d0 : ℤ) - 1 = ((d0 - 1 : ℕ) : ℤ) by push_cast [hd0ge]; ring,
        Int.natAbs_cast]
  have hZ1GDm1 : Y.Z 1 ≤ Y.Gi ((d0 : ℤ) - 1) := by
    have h := (h1i ((d0 : ℤ) - 2)).mpr ?_
    · rwa [show 1 + ((d0 : ℤ) - 2) = (d0 : ℤ) - 1 by ring] at h
    · rw [hd1eq]
      rw [show (d0 : ℤ) - 2 = ((d0 - 2 : ℕ) : ℤ) by push_cast [hd0ge2]; ring,
        Int.natAbs_cast]
      omega
  have hZ1j1 : ¬ Y.Z 1 ≤ Y.Gi ((d0 : ℤ) + 1) := by
    have h := h1.2.1
    rw [hd1eq] at h
    rwa [show (1 : ℤ) + ((d0 - 1 : ℕ) : ℤ) + 1 = (d0 : ℤ) + 1 by
      push_cast [hd0ge]; ring] at h
  have hR_ne : ⁅Y.Z 1, Y.Z (d0 : ℤ)⁆ ≠ ⊥ :=
    commutator_Z_one_Z_ne_bot Y H hZ hDodd hZ1GD hZ1GDm1 hZ1j1
  have hZD2eq : Y.Z ((d0 : ℤ) - 1) = Y.Z 2 :=
    Z_pred_eq_Z_two Y H hZ hDodd hZ1GD hZ1GDm1 hZD1 hZD2 hR_ne
  have htrans : Y.Z ((d0 : ℤ) - 1) = conjSub (Y.τ ^ ((m : ℤ) - 1)) (Y.Z 2) := by
    rw [show (d0 : ℤ) - 1 = 2 + 2 * ((m : ℤ) - 1) by omega, Y.Z_add]
  have hZ2inv : conjSub (Y.τ ^ ((m : ℤ) - 1)) (Y.Z 2) = Y.Z 2 := by
    rw [← htrans, hZD2eq]
  have hk0 : (m : ℤ) - 1 = 0 :=
    eq_zero_of_conjSub_zpow_Z_two Y h2i hZ2inv
  have hm1 : m = 1 := by omega
  have hD3 : (d0 : ℤ) = 3 := by omega
  exact_mod_cast hD3

theorem s52_step9 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.HasB 0 3 ∧ Y.HasB 1 2 := by
  obtain ⟨d0, h0⟩ := exists_hasB Y H 0 hZ
  obtain ⟨-, -, -, -, -, -, -, hZt1⟩ := Y.s52_step8 H hZ
  obtain ⟨d1, h1⟩ := exists_hasB Y H 1 hZt1
  obtain ⟨hd0ge, hd1eq, hd0odd⟩ := hasB_one_eq_pred_of_hasB_zero Y H hZ h0 h1
  have hd0three : d0 = 3 := d0_eq_three Y H hZ h0 h1 hd0ge hd1eq hd0odd
  refine ⟨?_, ?_⟩
  · rwa [hd0three] at h0
  · rw [hd1eq, hd0three] at h1
    simpa using h1

theorem s52_step9_cons (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    (∀ i : ℤ, Even i → Y.HasB i 3) ∧ (∀ i : ℤ, Odd i → Y.HasB i 2) := by
  obtain ⟨h0, h1⟩ := Y.s52_step9 H hZ
  refine ⟨fun i hi => (Y.hasB_iff_of_even (i := i) (j := 0) (by simpa using hi) 3).mpr h0,
    fun i hi => ?_⟩
  obtain ⟨m, hm⟩ := hi
  exact (Y.hasB_iff_of_even (i := i) (j := 1) ⟨m, by omega⟩ 2).mpr h1

private theorem Z_le_stabilizer_iff_of_hasB (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {i : ℤ}
    {d : ℕ} (hd : Y.HasB i d) (hds : d + 1 ≤ s) (w : V) :
    Y.Z i ≤ MulAction.stabilizer G w ↔ Γ.dist (Y.vert i) w ≤ d := by
  constructor
  · intro hfix
    by_contra hle
    rw [not_le] at hle
    obtain ⟨P, hP0, hPe⟩ := IsTree.exists_arc_between Y.hyp.isTree (Y.vert i) w
    have hfix0 : Y.Z i ≤ MulAction.stabilizer G (P.vert 0) := by
      rw [hP0]
      exact Y.Z_le_Gi i
    have hfixk : Y.Z i ≤ MulAction.stabilizer G (P.vert (d + 1)) := by
      intro z hz
      rw [MulAction.mem_stabilizer_iff]
      have h0 : z • P.vert 0 = P.vert 0 :=
        MulAction.mem_stabilizer_iff.mp (hfix0 hz)
      have hn : z • P.vert (Γ.dist (Y.vert i) w) = P.vert (Γ.dist (Y.vert i) w) := by
        rw [hPe]
        exact MulAction.mem_stabilizer_iff.mp (hfix hz)
      exact Arc.fixes_of_ends Y.hyp.isTree Y.hyp.adj_smul P h0 hn (d + 1) (by omega)
    set Q : Arc Γ (d + 1) := Arc.take P (d + 1) (by omega) with hQ
    have hQ0 : Q.vert 0 = Y.vert i := hP0
    have hQk : Q.vert (d + 1) = P.vert (d + 1) := rfl
    obtain ⟨g, hg⟩ := arc_conj_of_le Y.hyp.adj_smul
      (fun v a b ha hb => Y.hyp.locTrans ha hb) H.sing hds
      (Y.line.arc i (d + 1)) Q 1 (by rw [hQ0]; simp [Line.arc])
    have hg0 : g • Y.vert i = Y.vert i := by
      have h := hg 0 (by omega)
      rw [hQ0] at h
      simpa [Line.arc] using h
    have hgGi : g ∈ Y.Gi i := MulAction.mem_stabilizer_iff.mpr hg0
    have hgend : g • Y.vert (i + ((d + 1 : ℕ) : ℤ)) = P.vert (d + 1) := by
      have h := hg (d + 1) (by omega)
      rwa [hQk] at h
    have hZfix : Y.Z i ≤ Y.Gi (i + ((d + 1 : ℕ) : ℤ)) := by
      intro z hz
      have hz' : g * z * g⁻¹ ∈ Y.Z i := by
        have hnorm := Y.Z_normal i g hgGi
        rw [← hnorm]
        exact mul_mem_conjSub hz
      have hfix_end : (g * z * g⁻¹) • P.vert (d + 1) = P.vert (d + 1) :=
        MulAction.mem_stabilizer_iff.mp (hfixk hz')
      have hzend : z • (g⁻¹ • P.vert (d + 1)) = g⁻¹ • P.vert (d + 1) := by
        calc z • (g⁻¹ • P.vert (d + 1)) = (z * g⁻¹) • P.vert (d + 1) :=
              (mul_smul z g⁻¹ _).symm
          _ = (g⁻¹ * (g * z * g⁻¹)) • P.vert (d + 1) := by congr 1; group
          _ = g⁻¹ • ((g * z * g⁻¹) • P.vert (d + 1)) := mul_smul g⁻¹ _ _
          _ = g⁻¹ • P.vert (d + 1) := by rw [hfix_end]
      have hgv : g⁻¹ • P.vert (d + 1) = Y.vert (i + ((d + 1 : ℕ) : ℤ)) := by
        rw [← hgend, smul_smul, inv_mul_cancel, one_smul]
      rw [hgv] at hzend
      exact MulAction.mem_stabilizer_iff.mpr hzend
    have hZfix' : Y.Z i ≤ Y.Gi (i + (d : ℤ) + 1) := by
      rw [show i + ((d + 1 : ℕ) : ℤ) = i + (d : ℤ) + 1 by push_cast; ring] at hZfix
      exact hZfix
    exact hd.2.1 hZfix'
  · intro hle
    have hdist : Γ.dist (Y.vert i) (Y.vert (i + (d : ℤ))) = d := by
      have h := Line.dist_eq Y.hyp.isTree Y.line (i := i) (j := i + (d : ℤ)) (by omega)
      rwa [show i + (d : ℤ) - i = (d : ℤ) by ring, Int.toNat_natCast] at h
    have hfixd : Y.Z i ≤ MulAction.stabilizer G (Y.vert (i + (d : ℤ))) :=
      hd.1 (d : ℤ) (by simp)
    exact Y.Z_fixes_of_dist i H.sing (by omega) hdist hfixd w hle

theorem vertZ_le_stabilizer_iff (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (i : ℤ) (g : G) (w : V) :
    vertZ (G := G) (g • Y.vert i) ≤ MulAction.stabilizer G w ↔
      Γ.dist (g • Y.vert i) w ≤ if Even i then 3 else 2 := by
  have hconj : vertZ (G := G) (g • Y.vert i) = conjSub g (Y.Z i) := by
    rw [vertZ_smul, ← Y.Z_eq_vertZ i]
  rw [hconj, conjSub_le_iff, ← stabilizer_smul_eq_conjSub]
  have hdist : Γ.dist (g • Y.vert i) w = Γ.dist (Y.vert i) (g⁻¹ • w) := by
    have h := IsTree.dist_smul Y.hyp.isTree Y.hyp.adj_smul g (Y.vert i) (g⁻¹ • w)
    rwa [smul_inv_smul] at h
  rw [hdist]
  obtain ⟨h3, h2⟩ := Y.s52_step9_cons H hZ
  have h5 : 5 ≤ s := H.five_le
  by_cases hi : Even i
  · rw [if_pos hi]
    exact Y.Z_le_stabilizer_iff_of_hasB H (h3 i hi) (by omega) (g⁻¹ • w)
  · rw [if_neg hi]
    exact Y.Z_le_stabilizer_iff_of_hasB H (h2 i (Int.not_even_iff_odd.mp hi)) (by omega)
      (g⁻¹ • w)

@[expose] def VNbr0 (Y : Setup Γ G) : Subgroup G :=
  ⨆ g ∈ Y.L 0, (Y.Z 1).map (MulAut.conj g).toMonoidHom

abbrev VNbr2 (Y : Setup Γ G) : Subgroup G := (Y.shift 2).VNbr0

theorem L_zero_trans (Y : Setup Γ G) {a b : V}
    (ha : Γ.Adj (Y.vert 0) a) (hb : Γ.Adj (Y.vert 0) b) :
    ∃ g ∈ Y.L 0, g • a = b :=
  (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).trans a b ha hb

theorem dist_nbr_le_two (Y : Setup Γ G) {a b : V}
    (ha : Γ.Adj (Y.vert 0) a) (hb : Γ.Adj (Y.vert 0) b) : Γ.dist a b ≤ 2 := by
  have h := SimpleGraph.dist_le
    (SimpleGraph.Walk.cons ha.symm (SimpleGraph.Walk.cons hb SimpleGraph.Walk.nil))
  rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_nil] at h
  exact h

private theorem Z_one_le_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 1 ≤ Y.Q 0 :=
  Y.Z_le_Q_of_le_Gi 1 (-1) 0
    (by simpa using (Y.s52_step9 H hZ).2.1 (-2) (by norm_num))
    (Or.inr ⟨by norm_num, by norm_num⟩)

private theorem vertZ_le_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : vertZ (G := G) (u : V) ≤ Y.Q 0 := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := Z_one_le_Q_zero Y H hZ
  have hQconj : conjSub g (Y.Q 0) = Y.Q 0 := by
    show conjSub g (pCoreOf 2 (Y.Gi 0)) = pCoreOf 2 (Y.Gi 0)
    rw [← pCoreOf_conjSub, conjSub_eq_of_mem (Y.L_le_Gi 0 hg)]
  rw [← hgu, vertZ_smul, ← hQconj]
  exact conjSub_mono g hZ1Q0

theorem VNbr0_eq_iSup (Y : Setup Γ G) :
    Y.VNbr0 = ⨆ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  apply le_antisymm
  · unfold VNbr0
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hmem : Γ.Adj (Y.vert 0) (g • Y.vert 1) := by
      have hg0 : g • Y.vert 0 = Y.vert 0 :=
        MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 0 hg)
      rw [← hg0]
      exact (Y.hyp.adj_smul g (Y.vert 0) (Y.vert 1)).2 h01
    have hEq : (Y.Z 1).map (MulAut.conj g).toMonoidHom = vertZ (G := G) (g • Y.vert 1) := by
      rw [Setup.Z_eq_vertZ]
      exact (vertZ_smul (G := G) g (Y.vert 1)).symm
    rw [hEq]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
      ⟨g • Y.vert 1, hmem⟩
  · refine iSup_le fun u => ?_
    obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
    rw [← hgu, vertZ_smul]
    unfold VNbr0
    exact le_iSup₂_of_le g hg (le_refl ((Y.Z 1).map (MulAut.conj g).toMonoidHom))

private theorem VNbr0_le_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr0 ≤ Y.Q 0 := by
  rw [VNbr0_eq_iSup Y]
  exact iSup_le fun u => vertZ_le_Q_zero Y H hZ u

theorem vertZ_le_stabilizer_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (u : Γ.neighborSet (Y.vert 0)) {w : V} (hw : Γ.Adj (Y.vert 0) w) :
    vertZ (G := G) (u : V) ≤ MulAction.stabilizer G w := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
  have hd : Γ.dist (u : V) w ≤ 2 := dist_nbr_le_two Y u.2 hw
  rw [← hgu]
  refine (vertZ_le_stabilizer_iff Y H hZ 1 g w).mpr ?_
  rw [if_neg (by norm_num : ¬ Even (1 : ℤ))]
  simpa [hgu] using hd

theorem VNbr0_fixes_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : G} (hx : x ∈ Y.VNbr0) {w : V} (hw : Γ.Adj (Y.vert 0) w) : x • w = w := by
  have hle : Y.VNbr0 ≤ MulAction.stabilizer G w := by
    rw [VNbr0_eq_iSup Y]
    exact iSup_le fun u => vertZ_le_stabilizer_nbr Y H hZ u hw
  exact MulAction.mem_stabilizer_iff.mp (hle hx)

private theorem Gi_zero_le_normalizer_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Gi 0 ≤ Subgroup.normalizer (Y.VNbr0 : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub g Y.VNbr0 = Y.VNbr0
  have hg0 : g • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp hg
  have hginv : g⁻¹ ∈ Y.Gi 0 := (Y.Gi 0).inv_mem hg
  rw [VNbr0_eq_iSup Y]
  rw [conjSub, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun u => ?_
    have hEq : Subgroup.map (MulAut.conj g).toMonoidHom (vertZ (G := G) (u : V))
        = conjSub g (vertZ (G := G) (u : V)) := rfl
    rw [hEq, ← vertZ_smul]
    have hmem : Γ.Adj (Y.vert 0) (g • (u : V)) := by
      have h := (Y.hyp.adj_smul g (Y.vert 0) (u : V)).mpr u.2
      rwa [hg0] at h
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
      ⟨g • (u : V), hmem⟩
  · refine iSup_le fun u => ?_
    have hmem : Γ.Adj (Y.vert 0) (g⁻¹ • (u : V)) := by
      have h := (Y.hyp.adj_smul g⁻¹ (Y.vert 0) (u : V)).mpr u.2
      rwa [MulAction.mem_stabilizer_iff.mp hginv] at h
    have hle := le_iSup (fun u : Γ.neighborSet (Y.vert 0) =>
      Subgroup.map (MulAut.conj g).toMonoidHom (vertZ (G := G) (u : V)))
      ⟨g⁻¹ • (u : V), hmem⟩
    have heq : Subgroup.map (MulAut.conj g).toMonoidHom
        (vertZ (G := G) (g⁻¹ • (u : V))) = vertZ (G := G) (u : V) := by
      rw [show Subgroup.map (MulAut.conj g).toMonoidHom
          (vertZ (G := G) (g⁻¹ • (u : V))) = conjSub g (vertZ (G := G) (g⁻¹ • (u : V)))
          from rfl, ← vertZ_smul]
      simp
    rwa [heq] at hle

theorem Z_zero_le_vertZ (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : Y.Z 0 ≤ vertZ (G := G) (u : V) := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
  obtain ⟨hcenter, -, -, -, h5, -, -, -⟩ := Y.s52_step8 H hZ
  have hZ1 : Y.Z 0 ≤ Y.Z 1 := by
    rw [h5]
    exact le_sup_left
  have hgZ : conjSub g (Y.Z 0) = Y.Z 0 := by
    rw [hcenter, centerOf, conjSub_inf, conjSub_eq_of_mem hg, ← conjSub_centralizer,
      conjSub_eq_of_mem hg]
  rw [← hgu, vertZ_smul]
  rw [← hgZ]
  exact conjSub_mono g (by simpa [Setup.Z_eq_vertZ] using hZ1)

theorem card_vertZ_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : Nat.card (vertZ (G := G) (u : V)) = 4 := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
  rw [← hgu, vertZ_smul]
  rw [show conjSub g (vertZ (G := G) (Y.vert 1)) =
      (vertZ (G := G) (Y.vert 1)).map (MulAut.conj g).toMonoidHom from rfl,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  simpa [Setup.Z_eq_vertZ] using (s52_step8_Z Y H hZ 1 (by norm_num)).2

theorem exists_mem_vertZ_not_mem_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (u : Γ.neighborSet (Y.vert 0)) :
    ∃ x ∈ vertZ (G := G) (u : V), x ∉ Y.Z 0 := by
  have hZ0le : Y.Z 0 ≤ vertZ (G := G) (u : V) := Y.Z_zero_le_vertZ H hZ u
  haveI : Finite ↥(Y.Z 0) := Nat.finite_of_card_ne_zero (by
    rw [(s52_step8 Y H hZ).2.2.2.2.2.2.1]
    norm_num)
  have hne : ¬ vertZ (G := G) (u : V) ≤ Y.Z 0 := by
    intro hle
    have hcardle : Nat.card (vertZ (G := G) (u : V)) ≤ Nat.card (Y.Z 0) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    rw [Y.card_vertZ_nbr H hZ u, (s52_step8 Y H hZ).2.2.2.2.2.2.1] at hcardle
    norm_num at hcardle
  exact Set.not_subset.mp hne

theorem isElemAbelian_vertZ_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (u : Γ.neighborSet (Y.vert 0)) :
    IsElemAbelian 2 (vertZ (G := G) (u : V)) := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := Y.L_zero_trans (a := Y.vert 1) (b := (u : V)) h01 u.2
  rw [← hgu, vertZ_smul]
  exact (CFSG.Quasithin.F7.isElemAbelian_conjSub_iff (p := 2) g).mpr (by
    simpa [Setup.Z_eq_vertZ] using (s52_step8_Z Y H hZ 1 (by norm_num)).1)

private theorem relIndex_Z_zero_vertZ (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) :
    (Y.Z 0).relIndex (vertZ (G := G) (u : V)) = 2 := by
  have hle : Y.Z 0 ≤ vertZ (G := G) (u : V) := Z_zero_le_vertZ Y H hZ u
  have h := Subgroup.relIndex_mul_card (H := Y.Z 0) (K := vertZ (G := G) (u : V))
  rw [inf_eq_left.mpr hle, card_vertZ_nbr Y H hZ u,
    (s52_step8 Y H hZ).2.2.2.2.2.2.1] at h
  omega

private theorem commutator_Q_zero_vertZ (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {q : G} (hq : q ∈ Y.Q 0) (u : Γ.neighborSet (Y.vert 0)) {z : G}
    (hz : z ∈ vertZ (G := G) (u : V)) : ⁅q, z⁆ ∈ Y.Z 0 := by
  refine commutator_mem_of_relIndex_two_of_centralizes (relIndex_Z_zero_vertZ Y H hZ u) ?_
    (Subgroup.le_centralizer_iff.mp ((Y.Z_le_center 0).trans inf_le_right) hq) hz
  rw [← vertZ_smul, Y.Q_fixes_neighbors_vert 0 (u : V) u.2 q hq]

private theorem commutator_Q_zero_VNbr0_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : ⁅Y.Q 0, Y.VNbr0⁆ ≤ Y.Z 0 := by
  rw [Subgroup.commutator_le]
  intro q hq v hv
  rw [VNbr0_eq_iSup Y] at hv
  refine (Subgroup.iSup_induction (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
    hv (C := fun x => x ∈ Y.VNbr0 ∧ ⁅q, x⁆ ∈ Y.Z 0) ?_ ?_ ?_).2
  · intro u x hx
    refine ⟨?_, commutator_Q_zero_vertZ Y H hZ hq u hx⟩
    rw [VNbr0_eq_iSup Y]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u hx
  · exact ⟨Y.VNbr0.one_mem, by simp⟩
  · intro x y hx hy
    obtain ⟨hxV, hxZ⟩ := hx
    obtain ⟨hyV, hyZ⟩ := hy
    refine ⟨Y.VNbr0.mul_mem hxV hyV, ?_⟩
    have hxQ : x ∈ Y.Q 0 := VNbr0_le_Q_zero Y H hZ hxV
    have hcent : x * ⁅q, y⁆ * x⁻¹ = ⁅q, y⁆ := by
      have hcen : ⁅q, y⁆ ∈ centerOf (Y.Q 0) := Y.Z_le_center 0 hyZ
      have hcomm : x * ⁅q, y⁆ = ⁅q, y⁆ * x :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcen).2 x hxQ
      rw [hcomm]
      group
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hEq : ⁅q, x⁆ * x * ⁅q, y⁆ * x⁻¹ = ⁅q, x⁆ * ⁅q, y⁆ := by
      rw [show ⁅q, x⁆ * x * ⁅q, y⁆ * x⁻¹ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) from by group, hcent]
    rw [hEq]
    exact (Y.Z 0).mul_mem hxZ hyZ

private theorem relIndex_Q_of_fixes_nbr (Y : Setup Γ G) (i : ℤ) (hi : Y.n i = 1)
    {C : Subgroup G} (hC : C ≤ Y.L i) {a : V} (ha : Γ.Adj (Y.vert i) a)
    (hCa : C ≤ MulAction.stabilizer G a) (hCQ : ¬ C ≤ Y.Q i) :
    (C ⊓ Y.Q i).relIndex C = 2 := by
  let hN : IsLocL2 Γ G (Y.vert i) (Y.n i) (Y.L i) := Y.hyp.isLocL2_oTwoPrime (Y.vert i)
  have hfin := Y.hyp.finite_stab (Y.vert i)
  have hcard := (Y.hyp.valency (Y.vert i)).2
  have hn : 1 ≤ Y.n i := (Y.hyp.valency (Y.vert i)).1
  have hker : MonoidHom.ker hN.phi = (Y.Q i).subgroupOf (Y.L i) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  have hmaple : (C.subgroupOf (Y.L i)).map hN.phi ≤ hN.pointBorel a := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyC : ((y : Y.L i) : G) ∈ C := Subgroup.mem_subgroupOf.mp hy
    have hypoint : y ∈ hN.pointSubgroup a := by
      rw [hN.pointSubgroup_eq_stabilizer Y.hyp.adj_smul ha, MulAction.mem_stabilizer_iff]
      exact Subtype.ext (MulAction.mem_stabilizer_iff.mp (hCa hyC))
    have hcomap : y ∈ (hN.pointBorel a).comap hN.phi := by
      rw [← hN.pointSubgroup_eq_comap_pointBorel Y.hyp.adj_smul hfin hcard hn ha]
      exact hypoint
    exact hcomap
  have hcardB : Nat.card (hN.pointBorel a) = 2 := by
    have h := hN.card_pointBorel Y.hyp.adj_smul hfin hcard hn ha
    rw [h, hi]
    norm_num
  have hne : (C.subgroupOf (Y.L i)).map hN.phi ≠ ⊥ := by
    intro hbot
    apply hCQ
    intro x hx
    have hxL : x ∈ Y.L i := hC hx
    have hxsub : (⟨x, hxL⟩ : Y.L i) ∈ C.subgroupOf (Y.L i) :=
      Subgroup.mem_subgroupOf.mpr hx
    have hphi : hN.phi ⟨x, hxL⟩ = 1 := by
      have hmem : hN.phi ⟨x, hxL⟩ ∈ (C.subgroupOf (Y.L i)).map hN.phi :=
        Subgroup.mem_map_of_mem hN.phi hxsub
      rw [hbot] at hmem
      simpa using hmem
    exact (hN.phi_ker ⟨x, hxL⟩).mp hphi
  haveI : Finite ↥((C.subgroupOf (Y.L i)).map hN.phi) :=
    Finite.of_injective (Subgroup.inclusion hmaple) (Subgroup.inclusion_injective hmaple)
  have hge : 2 ≤ Nat.card ↥((C.subgroupOf (Y.L i)).map hN.phi) := by
    have h1 : Nat.card ↥((C.subgroupOf (Y.L i)).map hN.phi) ≠ 1 := fun h =>
      hne (Subgroup.card_eq_one.mp h)
    have hpos := Nat.card_pos (α := ↥((C.subgroupOf (Y.L i)).map hN.phi))
    omega
  have hcard2 : Nat.card ↥((C.subgroupOf (Y.L i)).map hN.phi) = 2 :=
    le_antisymm (le_trans (Nat.card_le_card_of_injective (Subgroup.inclusion hmaple)
      (Subgroup.inclusion_injective hmaple)) (le_of_eq hcardB)) hge
  have hrel : (Y.Q i).relIndex C = Nat.card ↥((C.subgroupOf (Y.L i)).map hN.phi) := by
    rw [← Subgroup.relIndex_subgroupOf hC, ← hker]
    exact Subgroup.relIndex_ker (f := hN.phi) (K := C.subgroupOf (Y.L i))
  have hrel' : (C ⊓ Y.Q i).relIndex C = (Y.Q i).relIndex C :=
    Subgroup.inf_relIndex_left C (Y.Q i)
  rw [hrel', hrel, hcard2]

private theorem Z_one_not_le_Q_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : ¬ Y.Z 1 ≤ Y.Q (-1) := by
  intro hle
  have hQfix : Y.Q (-1) ≤ MulAction.stabilizer G (Y.vert (-2)) := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert (-1) (Y.vert (-2)) (by simpa using (Y.adj (-2)).symm) q hq)
  have hZfix : Y.Z 1 ≤ MulAction.stabilizer G (Y.vert (-2)) := hle.trans hQfix
  have h9 : Y.HasB 1 2 := (Y.s52_step9 H hZ).2
  have h5 : 5 ≤ s := H.five_le
  have hdists : Γ.dist (Y.vert 1) (Y.vert (-2)) ≤ 2 :=
    (Z_le_stabilizer_iff_of_hasB Y H h9 (by omega : 2 + 1 ≤ s) (Y.vert (-2))).mp hZfix
  have hdist : Γ.dist (Y.vert 1) (Y.vert (-2)) = 3 := by
    have h := Line.dist_eq Y.hyp.isTree Y.line (i := -2) (j := 1) (by omega)
    have h3 : ((1 : ℤ) - (-2)).toNat = 3 := by norm_num
    rw [h3] at h
    rwa [SimpleGraph.dist_comm]
  omega

private theorem center_L_neg_one_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : centerOf (Y.L (-1)) = ⊥ := by
  obtain ⟨-, -, h3, -, -, -, -, -⟩ := Y.s52_step8 H hZ
  have hL : Y.L (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.L 1) := by
    have h := Y.L_add (-1) 1
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
    exact h
  rw [hL, centerOf_conjSub, h3, conjSub_bot]

private theorem Z_one_not_le_centralizer_Z_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ¬ Y.Z 1 ≤ Subgroup.centralizer (Y.Z (-1) : Set G) := by
  intro hAcent
  have h9 : Y.HasB 1 2 := (Y.s52_step9 H hZ).2
  have hZ1Gm1 : Y.Z 1 ≤ Y.Gi (-1) := by
    have h := h9.1 (-2) (by norm_num)
    rwa [show (1 : ℤ) + (-2) = -1 by norm_num] at h
  have hZ1G0 : Y.Z 1 ≤ Y.Gi 0 := by
    have h := h9.1 (-1) (by norm_num)
    rwa [show (1 : ℤ) + (-1) = 0 by norm_num] at h
  have hZ1L : Y.Z 1 ≤ Y.L (-1) :=
    le_oTwoPrime_of_isPGroup (Y.isPGroup_Z 1) hZ1Gm1
  have hAa : Y.Z 1 ≤ MulAction.stabilizer G (Y.vert 0) := hZ1G0
  have hZ1nQ : ¬ Y.Z 1 ≤ Y.Q (-1) := Z_one_not_le_Q_neg_one Y H hZ
  have h01 : Γ.Adj (Y.vert (-1)) (Y.vert 0) := Y.adj (-1)
  have hm2 : Γ.Adj (Y.vert (-1)) (Y.vert (-2)) := by simpa using (Y.adj (-2)).symm
  have h02 : Y.vert 0 ≠ Y.vert (-2) := by
    intro h
    have := Y.vert_injective h
    omega
  obtain ⟨g, hg, hg0⟩ :=
    (Y.hyp.isLocL2_oTwoPrime (Y.vert (-1))).trans (Y.vert 0) (Y.vert (-2)) h01 hm2
  have hB_le_L : conjSub g (Y.Z 1) ≤ Y.L (-1) := by
    have h1 : conjSub g (Y.Z 1) ≤ conjSub g (Y.L (-1)) := conjSub_mono g hZ1L
    rwa [conjSub_eq_of_mem hg] at h1
  have hB_fix : conjSub g (Y.Z 1) ≤ MulAction.stabilizer G (Y.vert (-2)) := by
    have hconj := stabilizer_smul_eq_conjSub (G := G) g (Y.vert 0)
    rw [hg0] at hconj
    rw [hconj]
    exact conjSub_mono g hAa
  have hBnQ : ¬ conjSub g (Y.Z 1) ≤ Y.Q (-1) := by
    intro hleB
    apply hZ1nQ
    have hQconj : conjSub g⁻¹ (Y.Q (-1)) = Y.Q (-1) := by
      show conjSub g⁻¹ (pCoreOf 2 (Y.Gi (-1))) = pCoreOf 2 (Y.Gi (-1))
      rw [← pCoreOf_conjSub, conjSub_eq_of_mem (Y.L_le_Gi (-1) ((Y.L (-1)).inv_mem hg))]
    rw [← hQconj]
    exact (conjSub_le_iff g).mp hleB
  have hn_neg : Y.n (-1) = 1 := by
    have h := Y.n_add (-1) 1
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num, H.n_one] at h
    exact h
  have hidxA : (Y.Z 1 ⊓ Y.Q (-1)).relIndex (Y.Z 1) = 2 ^ Y.n (-1) := by
    have h := relIndex_Q_of_fixes_nbr Y (-1) hn_neg hZ1L h01 hAa hZ1nQ
    rw [hn_neg]
    simpa using h
  have hidxB : (conjSub g (Y.Z 1) ⊓ Y.Q (-1)).relIndex (conjSub g (Y.Z 1)) = 2 ^ Y.n (-1) := by
    have h := relIndex_Q_of_fixes_nbr Y (-1) hn_neg hB_le_L hm2 hB_fix hBnQ
    rw [hn_neg]
    simpa using h
  have hLsup := L_eq_sup_of_fixes Y (-1) h01 hm2 h02 hZ1L hB_le_L hAa hB_fix hidxA hidxB
  have hQcent : Y.Q (-1) ≤ Subgroup.centralizer (Y.Z (-1) : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((Y.Z_le_center (-1)).trans inf_le_right)
  have hBcent : conjSub g (Y.Z 1) ≤ Subgroup.centralizer (Y.Z (-1) : Set G) := by
    refine (conjSub_mono g hAcent).trans ?_
    rw [← conjSub_centralizer g (Y.Z (-1)), Y.Z_normal (-1) g (Y.L_le_Gi (-1) hg)]
  have hLcent : Y.L (-1) ≤ Subgroup.centralizer (Y.Z (-1) : Set G) := by
    rw [hLsup]
    exact sup_le (sup_le hAcent hBcent) hQcent
  have hZcent : Y.Z (-1) ≤ Subgroup.centralizer (Y.L (-1) : Set G) :=
    Subgroup.le_centralizer_iff.mpr hLcent
  have hZleCenter : Y.Z (-1) ≤ centerOf (Y.L (-1)) :=
    le_inf (le_oTwoPrime_of_isPGroup (Y.isPGroup_Z (-1)) (Y.Z_le_Gi (-1))) hZcent
  rw [center_L_neg_one_eq_bot Y H hZ] at hZleCenter
  have hbotZ : Y.Z (-1) = ⊥ := le_bot_iff.mp hZleCenter
  have hcard4 := (s52_step8_Z Y H hZ (-1) (by norm_num)).2
  rw [hbotZ, Subgroup.card_bot] at hcard4
  norm_num at hcard4

private theorem VNbr0_commutator_eq_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    ⁅Y.VNbr0, Y.VNbr0⁆ = Y.Z 0 := by
  have hle : ⁅Y.VNbr0, Y.VNbr0⁆ ≤ Y.Z 0 :=
    (Subgroup.commutator_mono (VNbr0_le_Q_zero Y H hZ) le_rfl).trans
      (commutator_Q_zero_VNbr0_le Y H hZ)
  obtain ⟨-, -, -, -, -, -, hcard0, -⟩ := Y.s52_step8 H hZ
  have hZ1V : Y.Z 1 ≤ Y.VNbr0 := by
    rw [VNbr0_eq_iSup Y]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
      ⟨Y.vert 1, by simpa using Y.adj (0 : ℤ)⟩
  have hZmV : Y.Z (-1) ≤ Y.VNbr0 := by
    rw [VNbr0_eq_iSup Y]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
      ⟨Y.vert (-1), by simpa using (Y.adj (-1)).symm⟩
  have hne : ⁅Y.VNbr0, Y.VNbr0⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ⁅Y.Z 1, Y.Z (-1)⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono hZ1V hZmV).trans (le_of_eq hbot))
    exact Z_one_not_le_centralizer_Z_neg_one Y H hZ
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  haveI : Finite ↥(Y.Z 0) :=
    Nat.finite_of_card_ne_zero (α := ↥(Y.Z 0)) (by rw [hcard0]; norm_num)
  haveI : Finite ↥⁅Y.VNbr0, Y.VNbr0⁆ :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hcardle : Nat.card ↥⁅Y.VNbr0, Y.VNbr0⁆ ≤ 2 := by
    calc Nat.card ↥⁅Y.VNbr0, Y.VNbr0⁆
        ≤ Nat.card ↥(Y.Z 0) := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      _ = 2 := hcard0
  have hcardne : Nat.card ↥⁅Y.VNbr0, Y.VNbr0⁆ ≠ 1 := fun h =>
    hne (Subgroup.card_eq_one.mp h)
  have hge : 2 ≤ Nat.card ↥⁅Y.VNbr0, Y.VNbr0⁆ := by
    have hpos := Nat.card_pos (α := ↥⁅Y.VNbr0, Y.VNbr0⁆)
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard0]; exact hge)

theorem VNbr0_props (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr0 ≤ Y.Q 0 ∧ Y.Gi 0 ≤ Subgroup.normalizer (Y.VNbr0 : Set G) ∧
      ⁅Y.Q 0, Y.VNbr0⁆ ≤ Y.Z 0 ∧ ⁅Y.VNbr0, Y.VNbr0⁆ = Y.Z 0 := by
  exact ⟨VNbr0_le_Q_zero Y H hZ, Gi_zero_le_normalizer_VNbr0 Y H hZ,
    commutator_Q_zero_VNbr0_le Y H hZ, VNbr0_commutator_eq_Z Y H hZ⟩

theorem VNbr0_isPGroup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    IsPGroup 2 Y.VNbr0 :=
  (pCoreOf_isPGroup' (Y.Gi 0)).to_le (VNbr0_le_Q_zero Y H hZ)

theorem VNbr0_le_Gi_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr0 ≤ Y.Gi 1 := by
  have hle : Y.VNbr0 ≤ MulAction.stabilizer G (Y.vert 1) := by
    rw [VNbr0_eq_iSup Y]
    exact iSup_le fun u => vertZ_le_stabilizer_nbr Y H hZ u (by simpa using Y.adj 0)
  exact hle

theorem VNbr0_le_L_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr0 ≤ Y.L 1 :=
  le_oTwoPrime_of_isPGroup (VNbr0_isPGroup Y H hZ) (VNbr0_le_Gi_one Y H hZ)

theorem VNbr2_le_Q_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr2 ≤ Y.Q 2 := by
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  simpa using (VNbr0_props (Y.shift 2) (H.shift_two 1) hZ2).1

theorem VNbr2_le_Gi_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr2 ≤ Y.Gi 1 := by
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  rw [VNbr2, VNbr0_eq_iSup (Y.shift 2)]
  exact iSup_le fun u => vertZ_le_stabilizer_nbr (Y.shift 2) (H.shift_two 1) hZ2 u
    (by simpa using (Y.adj 1).symm)

theorem VNbr2_le_L_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr2 ≤ Y.L 1 :=
  le_oTwoPrime_of_isPGroup
    ((pCoreOf_isPGroup' ((Y.shift 2).Gi 0)).to_le (VNbr2_le_Q_two Y H hZ))
    (by simpa using VNbr2_le_Gi_one Y H hZ)

private theorem Z_two_le_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 2 ≤ Y.Q 0 :=
  Y.Z_le_Q_of_le_Gi 2 (-1) 0
    (by simpa using ((Y.s52_step9_cons H hZ).1 2 (by norm_num)).1 (-3) (by norm_num))
    (Or.inr ⟨by norm_num, by norm_num⟩)

private theorem Z_zero_le_Q_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 0 ≤ Y.Q 2 :=
  Y.Z_le_Q_of_le_Gi 0 3 2
    (by simpa using (Y.s52_step9 H hZ).1.1 3 (by norm_num))
    (Or.inr ⟨by norm_num, by norm_num⟩)

private theorem Z_neg_one_not_le_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    ¬ Y.Z (-1) ≤ Y.Q 1 := by
  intro hle
  have hQfix : Y.Q 1 ≤ MulAction.stabilizer G (Y.vert 2) := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr (Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (Y.adj 1) q hq)
  have hZfix : Y.Z (-1) ≤ MulAction.stabilizer G (Y.vert 2) := hle.trans hQfix
  have h9 : Y.HasB (-1) 2 :=
    (hasB_iff_of_even Y (i := -1) (j := 1) (by norm_num) 2).mpr ((Y.s52_step9 H hZ).2)
  have h5 : 5 ≤ s := H.five_le
  have hdists : Γ.dist (Y.vert (-1)) (Y.vert 2) ≤ 2 :=
    (Z_le_stabilizer_iff_of_hasB Y H h9 (by omega : 2 + 1 ≤ s) (Y.vert 2)).mp hZfix
  have hdist : Γ.dist (Y.vert (-1)) (Y.vert 2) = 3 := by
    have h := Line.dist_eq Y.hyp.isTree Y.line (i := -1) (j := 2) (by omega)
    have h3 : ((2 : ℤ) - (-1)).toNat = 3 := by norm_num
    rwa [h3] at h
  omega

private theorem adj_zero_neg_one (Y : Setup Γ G) : Γ.Adj (Y.vert 0) (Y.vert (-1)) := by
  simpa using (Y.adj (-1)).symm

private theorem L_one_le_VNbr0_sup_VNbr2_sup_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.L 1 ≤ Y.VNbr0 ⊔ Y.VNbr2 ⊔ Y.Q 1 := by
  have hH2 : (Y.shift 2).Sec5Hyp s n₀ := H.shift_two 1
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  have hV0L : Y.VNbr0 ≤ Y.L 1 := VNbr0_le_L_one Y H hZ
  have hV2L : Y.VNbr2 ≤ Y.L 1 := VNbr2_le_L_one Y H hZ
  have hAa : Y.VNbr0 ≤ MulAction.stabilizer G (Y.vert 0) :=
    (VNbr0_le_Q_zero Y H hZ).trans (Y.Q_le_Gi 0)
  have hBb : Y.VNbr2 ≤ MulAction.stabilizer G (Y.vert 2) := by
    simpa using (VNbr2_le_Q_two Y H hZ).trans (Y.Q_le_Gi 2)
  have hV0nQ : ¬ Y.VNbr0 ≤ Y.Q 1 := by
    intro hle
    apply Z_neg_one_not_le_Q_one Y H hZ
    have hZmV : Y.Z (-1) ≤ Y.VNbr0 := by
      rw [VNbr0_eq_iSup Y]
      exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
        ⟨Y.vert (-1), adj_zero_neg_one Y⟩
    exact hZmV.trans hle
  have hV2nQ : ¬ Y.VNbr2 ≤ Y.Q 1 := by
    have hQeq : (Y.shift 2).Q (-1) = Y.Q 1 := by
      rw [Setup.shift_Q]
      norm_num
    rw [← hQeq]
    intro hle
    apply Z_one_not_le_Q_neg_one (Y.shift 2) hH2 hZ2
    have hZ3 : (Y.shift 2).Z 1 ≤ (Y.shift 2).VNbr0 := by
      rw [VNbr0_eq_iSup (Y.shift 2)]
      exact le_iSup (fun u : Γ.neighborSet ((Y.shift 2).vert 0) => vertZ (G := G) (u : V))
        ⟨(Y.shift 2).vert 1, by simpa using (Y.shift 2).adj 0⟩
    exact hZ3.trans hle
  have hn1 : Y.n 1 = 1 := H.n_one
  have hAidx : (Y.VNbr0 ⊓ Y.Q 1).relIndex Y.VNbr0 = 2 ^ Y.n 1 := by
    have h := relIndex_Q_of_fixes_nbr Y 1 hn1 hV0L (a := Y.vert 0)
      (by simpa using (Y.adj 0).symm) hAa hV0nQ
    rw [hn1]
    simpa using h
  have hBidx : (Y.VNbr2 ⊓ Y.Q 1).relIndex Y.VNbr2 = 2 ^ Y.n 1 := by
    have hni : (Y.shift 2).n (-1) = 1 := by
      show Y.n (-1 + 2) = 1
      rw [show (-1 : ℤ) + 2 = 1 by norm_num]
      exact H.n_one
    have h := relIndex_Q_of_fixes_nbr (Y.shift 2) (-1) hni hV2L
      (a := (Y.shift 2).vert 0) (by simpa using (Y.adj 1)) hBb hV2nQ
    rw [hn1]
    simpa using h
  have hsup := L_eq_sup_of_fixes Y 1 (A := Y.VNbr0) (B := Y.VNbr2)
    (a := Y.vert 0) (b := Y.vert 2) (by simpa using (Y.adj 0).symm) (Y.adj 1)
    (by
      intro h
      have := Y.vert_injective h
      omega)
    hV0L hV2L hAa hBb hAidx hBidx
  exact le_of_eq hsup

theorem s52_A_normal (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.L 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) ∧
      Y.L 1 ≤ Y.VNbr0 ⊔ Y.VNbr2 ⊔ Y.Q 1 := by
  have hH2 : (Y.shift 2).Sec5Hyp s n₀ := H.shift_two 1
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  have hZ0A : Y.Z 0 ≤ Y.Q 0 ⊓ Y.Q 2 := le_inf (Y.Z_le_Q 0) (Z_zero_le_Q_two Y H hZ)
  have hZ2A : Y.Z 2 ≤ Y.Q 0 ⊓ Y.Q 2 := le_inf (Z_two_le_Q_zero Y H hZ) (Y.Z_le_Q 2)
  have hLsub : Y.L 1 ≤ Y.VNbr0 ⊔ Y.VNbr2 ⊔ Y.Q 1 :=
    L_one_le_VNbr0_sup_VNbr2_sup_Q_one Y H hZ
  refine ⟨?_, hLsub⟩
  have hV0N : Y.VNbr0 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_Q_zero_VNbr0_le Y H hZ)).trans hZ0A
  have hV2N : Y.VNbr2 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine ((Subgroup.commutator_mono inf_le_right le_rfl).trans ?_).trans hZ2A
    simpa using commutator_Q_zero_VNbr0_le (Y.shift 2) hH2 hZ2
  have hQ1N : Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub q (Y.Q 0 ⊓ Y.Q 2) = Y.Q 0 ⊓ Y.Q 2
    have hq0 : q ∈ Y.Gi 0 := MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 1 (Y.vert 0) (by simpa using (Y.adj 0).symm) q hq)
    have hq2 : q ∈ Y.Gi 2 := MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (Y.adj 1) q hq)
    have hc0 : conjSub q (Y.Q 0) = Y.Q 0 := by
      show conjSub q (pCoreOf 2 (Y.Gi 0)) = pCoreOf 2 (Y.Gi 0)
      rw [← pCoreOf_conjSub, conjSub_eq_of_mem hq0]
    have hc2 : conjSub q (Y.Q 2) = Y.Q 2 := by
      show conjSub q (pCoreOf 2 (Y.Gi 2)) = pCoreOf 2 (Y.Gi 2)
      rw [← pCoreOf_conjSub, conjSub_eq_of_mem hq2]
    rw [conjSub_inf, hc0, hc2]
  exact hLsub.trans (sup_le (sup_le hV0N hV2N) hQ1N)

private theorem smul_vert_zero_ne_of_orderOf_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : d • Y.vert 0 ≠ Y.vert 0 := by
  intro h0
  have hdG0 : d ∈ Y.Gi 0 := by
    change d ∈ MulAction.stabilizer G (Y.vert 0)
    rw [MulAction.mem_stabilizer_iff]
    exact h0
  have hS2 : IsPGroup 2 Y.S := by
    have h := Y.isSylowTwoOf_edgeSylow 0
    rw [Setup.edgeSylow_zero] at h
    exact h.2.1
  have hSle : Y.S ≤ Y.Gi 0 := by
    have h := Y.isSylowTwoOf_edgeSylow 0
    rw [Setup.edgeSylow_zero] at h
    exact h.1.trans inf_le_left
  have hmemS : d ∈ Y.S := Y.L_one_inf_Gi_zero_le_S H ⟨hd, hdG0⟩
  haveI : Finite ↥Y.S := finite_of_le_stabilizer Y.hyp (α := Y.vert 0) hSle
  have hdvd := Subgroup.orderOf_dvd_natCard Y.S hmemS
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  rw [hd3, hk] at hdvd
  have h32 : 3 ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdvd
  norm_num at h32

private theorem conjSub_Z_zero_ne_self_of_orderOf_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    conjSub d (Y.Z 0) ≠ Y.Z 0 := by
  classical
  have hdG1 : d ∈ Y.Gi 1 := Y.L_le_Gi 1 hd
  have hd2 : d ^ 2 ∈ Y.L 1 := (Y.L 1).pow_mem hd 2
  have hd2G1 : d ^ 2 ∈ Y.Gi 1 := Y.L_le_Gi 1 hd2
  have hd2_3 : orderOf (d ^ 2) = 3 :=
    (Nat.Coprime.orderOf_pow (by rw [hd3]; norm_num)).trans hd3
  have hfix1 : d • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hdG1
  have hfix1' : d ^ 2 • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hd2G1
  have hnotfix0 : d • Y.vert 0 ≠ Y.vert 0 :=
    smul_vert_zero_ne_of_orderOf_three Y H hd hd3
  have hnotfix02 : d ^ 2 • Y.vert 0 ≠ Y.vert 0 :=
    smul_vert_zero_ne_of_orderOf_three Y H hd2 hd2_3
  have hne_orbit : d • Y.vert 0 ≠ d ^ 2 • Y.vert 0 := by
    intro h
    have h' : Y.vert 0 = d • Y.vert 0 := by
      simpa [pow_two, mul_smul] using congrArg (fun v => d⁻¹ • v) h
    exact hnotfix0 h'.symm
  have hsub : ({Y.vert 0, d • Y.vert 0, d ^ 2 • Y.vert 0} : Set V) ⊆
      Γ.neighborSet (Y.vert 1) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · simpa using (Y.adj 0).symm
    · rw [SimpleGraph.mem_neighborSet, ← hfix1]
      exact (Y.hyp.adj_smul d (Y.vert 1) (Y.vert 0)).mpr (Y.adj 0).symm
    · rw [SimpleGraph.mem_neighborSet, ← hfix1']
      exact (Y.hyp.adj_smul (d ^ 2) (Y.vert 1) (Y.vert 0)).mpr (Y.adj 0).symm
  have hncard_orbit : ({Y.vert 0, d • Y.vert 0, d ^ 2 • Y.vert 0} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr
      ⟨_, _, _, hnotfix0.symm, hnotfix02.symm, hne_orbit, rfl⟩
  have hncard_nbr : (Γ.neighborSet (Y.vert 1)).ncard = 3 := Y.ncard_neighborSet_one H
  have hset := Set.eq_of_subset_of_ncard_le hsub (by rw [hncard_nbr, hncard_orbit])
    (Y.hyp.finite_neighborSet (Y.vert 1))
  have h2mem : Y.vert 2 ∈ ({Y.vert 0, d • Y.vert 0, d ^ 2 • Y.vert 0} : Set V) := by
    rw [hset]
    simpa using Y.adj 1
  intro hconj
  have hZeq : Y.Z 2 = Y.Z 0 := by
    rcases h2mem with h | h | h
    · exact absurd (Y.vert_injective h) (by norm_num)
    · calc Y.Z 2 = vertZ (Y.vert 2) := Y.Z_eq_vertZ 2
        _ = vertZ (d • Y.vert 0) := by rw [h]
        _ = conjSub d (vertZ (Y.vert 0)) := vertZ_smul d (Y.vert 0)
        _ = conjSub d (Y.Z 0) := by rw [Y.Z_eq_vertZ 0]
        _ = Y.Z 0 := hconj
    · calc Y.Z 2 = vertZ (Y.vert 2) := Y.Z_eq_vertZ 2
        _ = vertZ (d ^ 2 • Y.vert 0) := by rw [h]
        _ = conjSub (d ^ 2) (vertZ (Y.vert 0)) := vertZ_smul (d ^ 2) (Y.vert 0)
        _ = conjSub (d ^ 2) (Y.Z 0) := by rw [Y.Z_eq_vertZ 0]
        _ = Y.Z 0 := by
          rw [pow_two, conjSub_mul d d (Y.Z 0), hconj]
          exact hconj
  obtain ⟨-, -, -, -, -, h6c, hcard, -⟩ := Y.s52_step8 H hZ
  rw [hZeq, inf_idem] at h6c
  rw [h6c] at hcard
  simp at hcard

private theorem coe_eq_insert_of_card_eq_four {Z : Subgroup G} (hZ : Nat.card Z = 4) {a b c : G}
    (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : (Z : Set G) = {1, a, b, c} := by
  have hsub : ({1, a, b, c} : Set G) ⊆ (Z : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact ha
    · exact hb
    · exact hc
  have hncard : ({1, a, b, c} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({a, b, c} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ha1 h.symm
      · exact hb1 h.symm
      · exact hc1 h.symm
    have h2 : a ∉ ({b, c} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hab h
      · exact hac h
    have h3 : b ∉ ({c} : Set G) := by
      simpa using hbc
    rw [show ({1, a, b, c} : Set G) = insert 1 (insert a (insert b {c})) from rfl,
      Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3]
    simp
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hncardZ : (Z : Set G).ncard = 4 := hZ
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hncardZ, hncard]) (Set.toFinite _)).symm

theorem Z_one_inf_centralizer_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  classical
  obtain ⟨-, -, -, -, hsup, -, hcardZ0, -⟩ := Y.s52_step8 H hZ
  have hcardZ1 : Nat.card (Y.Z 1) = 4 :=
    (Y.s52_step8_Z H hZ 1 (by norm_num)).2
  have hd3pow : d ^ 3 = 1 := by
    have h := pow_orderOf_eq_one d
    rwa [hd3] at h
  have hnorm1 : conjSub d (Y.Z 1) = Y.Z 1 :=
    Y.Z_normal 1 d (Y.L_le_Gi 1 hd)
  have hnotZ0 : conjSub d (Y.Z 0) ≠ Y.Z 0 :=
    conjSub_Z_zero_ne_self_of_orderOf_three Y H hZ hd hd3
  obtain ⟨z0, hz0ne, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Y.Z 0))).mp hcardZ0
  have hz0mem : (z0 : G) ∈ Y.Z 0 := z0.2
  have hz0ne1 : (z0 : G) ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hZ0eq : ∀ x ∈ Y.Z 0, x = 1 ∨ x = (z0 : G) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr (congrArg Subtype.val (huniq ⟨x, hx⟩ ?_))
      intro hc
      exact hx1 (Subtype.ext_iff.mp hc)
  have hz0Z1 : (z0 : G) ∈ Y.Z 1 := by rw [hsup]; exact Subgroup.mem_sup_left hz0mem
  have hφmem : ∀ x ∈ Y.Z 1, d * x * d⁻¹ ∈ Y.Z 1 := by
    intro x hx
    have h := mul_mem_conjSub (g := d) (H := Y.Z 1) hx
    rwa [hnorm1] at h
  set w1 : G := d * (z0 : G) * d⁻¹ with hw1
  set w2 : G := d * w1 * d⁻¹ with hw2
  have hddd : d * d * d = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hd3pow
  have hinvddd : d⁻¹ * d⁻¹ * d⁻¹ = 1 := by
    have h := congrArg Inv.inv hddd
    simpa [mul_inv_rev, mul_assoc] using h
  have hφ3 : d * w2 * d⁻¹ = (z0 : G) := by
    rw [hw2, hw1]
    calc d * (d * (d * (z0 : G) * d⁻¹) * d⁻¹) * d⁻¹
        = (d * d * d) * (z0 : G) * (d⁻¹ * d⁻¹ * d⁻¹) := by group
      _ = (z0 : G) := by rw [hddd, hinvddd]; group
  have hw1Z1 : w1 ∈ Y.Z 1 := hφmem _ hz0Z1
  have hw2Z1 : w2 ∈ Y.Z 1 := hφmem _ hw1Z1
  have hw1ne1 : w1 ≠ 1 := by
    intro h
    apply hz0ne1
    have hz : (z0 : G) = d⁻¹ * w1 * d := by rw [hw1]; group
    rw [h] at hz
    simpa using hz
  have hw1nez : w1 ≠ (z0 : G) := by
    intro h
    rw [hw1] at h
    apply hnotZ0
    have hcen : d ∈ Subgroup.centralizer (Y.Z 0 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hZ0eq y hy with rfl | rfl
      · simp
      · calc (z0 : G) * d = (d * (z0 : G) * d⁻¹) * d := by rw [h]
          _ = d * (z0 : G) := by group
    have hdN : d ∈ Subgroup.normalizer (Y.Z 0 : Set G) :=
      Subgroup.centralizer_le_normalizer (Y.Z 0 : Set G) hcen
    rw [conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN
  have hw2ne1 : w2 ≠ 1 := by
    intro h
    have h3 := hφ3
    rw [h] at h3
    exact hz0ne1 (by simpa using h3.symm)
  have hw2nez : w2 ≠ (z0 : G) := by
    intro h
    apply hw1nez
    have h3 := hφ3
    rw [h, ← hw1] at h3
    exact h3
  have hw2new1 : w2 ≠ w1 := by
    intro h
    apply hw1nez
    have h3 := hφ3
    rw [h, ← hw2, h] at h3
    exact h3
  have hset : ({1, (z0 : G), w1, w2} : Set G) = (Y.Z 1 : Set G) :=
    (coe_eq_insert_of_card_eq_four hcardZ1 hz0Z1 hw1Z1 hw2Z1 hz0ne1 hw1ne1 hw2ne1
      hw1nez.symm hw2nez.symm hw2new1.symm).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxZ1, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hfix : d * x * d⁻¹ = x := by
    calc d * x * d⁻¹ = (x * d) * d⁻¹ := by rw [hxd]
      _ = x := by group
  have hxmem : x ∈ ({1, (z0 : G), w1, w2} : Set G) := by rw [hset]; exact hxZ1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
  rcases hxmem with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (hw1.trans hfix) hw1nez
  · exact absurd (hw2.trans hfix) hw2new1
  · exact absurd ((hφ3.symm.trans hfix).symm) hw2nez

private theorem three_dvd_relIndex_of_not_mem {W L : Subgroup G} {d : G} (hWL : W ≤ L)
    (hd : d ∈ L) (hd3 : orderOf d = 3)
    (hLN : L ≤ Subgroup.normalizer (W : Set G)) (hdW : d ∉ W) : 3 ∣ W.relIndex L := by
  have hcardZp : Nat.card ↥(Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hd3]
  haveI hfinZp : Finite ↥(Subgroup.zpowers d) :=
    Nat.finite_of_card_ne_zero (by rw [hcardZp]; norm_num)
  have hInt : W ⊓ Subgroup.zpowers d = ⊥ := by
    have hdvd : Nat.card ↥(W ⊓ Subgroup.zpowers d) ∣ 3 := by
      rw [← hcardZp]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card ↥(W ⊓ Subgroup.zpowers d) ≠ 3 := by
      intro h3
      have hEq : W ⊓ Subgroup.zpowers d = Subgroup.zpowers d := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
        rw [hcardZp, h3]
      have hdmem : d ∈ W ⊓ Subgroup.zpowers d := by
        rw [hEq]
        exact Subgroup.mem_zpowers d
      exact hdW (Subgroup.mem_inf.mp hdmem).1
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (H := W ⊓ Subgroup.zpowers d) h1
    · exact absurd h3 hne
  set A2 : Subgroup G := W ⊔ Subgroup.zpowers d with hA2
  have hWA2 : W ≤ A2 := le_sup_left
  have hZA2 : Subgroup.zpowers d ≤ A2 := le_sup_right
  have hA2L : A2 ≤ L := sup_le hWL (Subgroup.zpowers_le.mpr hd)
  have hrelA : W.relIndex A2 = 3 := by
    let W' : Subgroup ↥A2 := W.subgroupOf A2
    let R' : Subgroup ↥A2 := (Subgroup.zpowers d).subgroupOf A2
    haveI : W'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (hA2L.trans hLN)
    have hsup2 : W' ⊔ R' = ⊤ := by
      have h := (Subgroup.subgroupOf_sup hWA2 hZA2).symm
      rw [← hA2] at h
      simpa [W', R'] using h
    have h1 : W'.relIndex (W' ⊔ R') = W'.relIndex R' :=
      Subgroup.relIndex_sup_left R' W'
    rw [hsup2, Subgroup.relIndex_top_right] at h1
    calc W.relIndex A2 = W'.index := rfl
      _ = W'.relIndex R' := h1
      _ = W.relIndex (Subgroup.zpowers d) := Subgroup.relIndex_subgroupOf hZA2
      _ = (W ⊓ Subgroup.zpowers d).relIndex (Subgroup.zpowers d) :=
          (Subgroup.inf_relIndex_right W (Subgroup.zpowers d)).symm
      _ = (⊥ : Subgroup G).relIndex (Subgroup.zpowers d) := by rw [hInt]
      _ = Nat.card ↥(Subgroup.zpowers d) := Subgroup.relIndex_bot_left (Subgroup.zpowers d)
      _ = 3 := hcardZp
  have h := Subgroup.relIndex_mul_relIndex (H := W) (K := A2) (L := L) hWA2 hA2L
  rw [hrelA] at h
  exact ⟨A2.relIndex L, h.symm⟩

private theorem mem_VNbr0_sup_VNbr2_of_orderOf_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    d ∈ Y.VNbr0 ⊔ Y.VNbr2 := by
  classical
  have hH2 : (Y.shift 2).Sec5Hyp s n₀ := H.shift_two 1
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  set W : Subgroup G := Y.VNbr0 ⊔ Y.VNbr2 with hW
  have hV0L : Y.VNbr0 ≤ Y.L 1 := VNbr0_le_L_one Y H hZ
  have hV2L : Y.VNbr2 ≤ Y.L 1 := VNbr2_le_L_one Y H hZ
  have hWL : W ≤ Y.L 1 := sup_le hV0L hV2L
  have hQ1L : Y.Q 1 ≤ Y.L 1 := (Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1)
  have hsup : W ⊔ Y.Q 1 = Y.L 1 := by
    refine le_antisymm (sup_le hWL hQ1L) ?_
    have h := (s52_A_normal Y H hZ).2
    rw [hW]
    exact h
  have hQ1G0 : Y.Q 1 ≤ Y.Gi 0 := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 1 (Y.vert 0) (by simpa using (Y.adj 0).symm) q hq)
  have hQ1G2 : Y.Q 1 ≤ Y.Gi 2 := by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (Y.adj 1) q hq)
  have hQ1NV0 : Y.Q 1 ≤ Subgroup.normalizer (Y.VNbr0 : Set G) :=
    hQ1G0.trans (VNbr0_props Y H hZ).2.1
  have hQ1NV2 : Y.Q 1 ≤ Subgroup.normalizer (Y.VNbr2 : Set G) := by
    have h := (VNbr0_props (Y.shift 2) hH2 hZ2).2.1
    exact hQ1G2.trans (by simpa using h)
  have hQ1NW : Y.Q 1 ≤ Subgroup.normalizer (W : Set G) := by
    intro q hq
    have h1 := hQ1NV0 hq
    have h2 := hQ1NV2 hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [hW, Subgroup.map_sup, h1, h2]
  have hL1NW : Y.L 1 ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hsup]
    exact sup_le (Subgroup.le_normalizer (H := W)) hQ1NW
  have hIdx : W.relIndex (Y.L 1) = (W ⊓ Y.Q 1).relIndex (Y.Q 1) := by
    let W' : Subgroup ↥(Y.L 1) := W.subgroupOf (Y.L 1)
    let Q' : Subgroup ↥(Y.L 1) := (Y.Q 1).subgroupOf (Y.L 1)
    haveI : W'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hL1NW
    have hsup' : W' ⊔ Q' = ⊤ := by
      have h := (Subgroup.subgroupOf_sup hWL hQ1L).symm
      rw [hsup] at h
      simpa [W', Q'] using h
    have h1 : W'.relIndex (W' ⊔ Q') = W'.relIndex Q' :=
      Subgroup.relIndex_sup_left Q' W'
    rw [hsup', Subgroup.relIndex_top_right] at h1
    calc W.relIndex (Y.L 1) = W'.index := rfl
      _ = W'.relIndex Q' := h1
      _ = W.relIndex (Y.Q 1) := Subgroup.relIndex_subgroupOf hQ1L
      _ = (W ⊓ Y.Q 1).relIndex (Y.Q 1) :=
          (Subgroup.inf_relIndex_right W (Y.Q 1)).symm
  have h3rel : ¬ 3 ∣ (W ⊓ Y.Q 1).relIndex (Y.Q 1) := by
    haveI hG1fin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
    haveI hQ1fin : Finite ↥(Y.Q 1) :=
      Finite.of_injective (Subgroup.inclusion (Y.Q_le_Gi 1))
        (Subgroup.inclusion_injective _)
    have hQ1p : IsPGroup 2 (Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
    obtain ⟨k, hk⟩ := hQ1p.exists_card_eq
    have hdvd : (W ⊓ Y.Q 1).relIndex (Y.Q 1) ∣ Nat.card ↥(Y.Q 1) := by
      refine ⟨Nat.card ↥(W ⊓ Y.Q 1), ?_⟩
      have h := Subgroup.relIndex_mul_card (H := W ⊓ Y.Q 1) (K := Y.Q 1)
      rw [inf_assoc, inf_idem] at h
      exact h.symm
    intro h3
    have h32 : 3 ∣ Nat.card ↥(Y.Q 1) := h3.trans hdvd
    rw [hk] at h32
    exact absurd ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow h32) (by norm_num)
  by_contra hdW
  have h3dvd : 3 ∣ W.relIndex (Y.L 1) :=
    three_dvd_relIndex_of_not_mem hWL hd hd3 hL1NW hdW
  exact h3rel (hIdx ▸ h3dvd)

private theorem commutator_A_zpowers_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), Subgroup.zpowers d⁆ ≤ Y.Z 1 := by
  classical
  have hH2 : (Y.shift 2).Sec5Hyp s n₀ := H.shift_two 1
  have hZ2 : (Y.shift 2).Zt 0 = ⊥ := by
    show Y.Zt 2 = ⊥
    exact Zt_eq_bot_of_even Y hZ even_two
  obtain ⟨-, -, -, -, hsup, -, -, -⟩ := Y.s52_step8 H hZ
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := by rw [hsup]; exact le_sup_left
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := by rw [hsup]; exact le_sup_right
  have hAV0 : ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), Y.VNbr0⁆ ≤ Y.Z 0 :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_Q_zero_VNbr0_le Y H hZ)
  have hAV2 : ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), Y.VNbr2⁆ ≤ Y.Z 2 := by
    have h := commutator_Q_zero_VNbr0_le (Y.shift 2) hH2 hZ2
    refine (Subgroup.commutator_mono (H₁ := Y.Q 0 ⊓ Y.Q 2) (H₂ := Y.VNbr2)
      (K₁ := Y.Q 2) (K₂ := Y.VNbr2) inf_le_right le_rfl).trans ?_
    simpa using h
  have hV0L : Y.VNbr0 ≤ Y.L 1 := VNbr0_le_L_one Y H hZ
  have hV2L : Y.VNbr2 ≤ Y.L 1 := VNbr2_le_L_one Y H hZ
  have hL1Z1 : Y.L 1 ≤ Subgroup.normalizer (Y.Z 1 : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Y.Z_normal 1 l (Y.L_le_Gi 1 hl)
  have hSN : Subgroup.closure ((Y.VNbr0 : Set G) ∪ (Y.VNbr2 : Set G)) ≤
      Subgroup.normalizer (Y.Z 1 : Set G) := by
    rw [← Subgroup.sup_eq_closure]
    exact (sup_le hV0L hV2L).trans hL1Z1
  have hcomm : ∀ s ∈ ((Y.VNbr0 : Set G) ∪ (Y.VNbr2 : Set G)),
      ∀ a ∈ (Y.Q 0 ⊓ Y.Q 2 : Subgroup G), ⁅s, a⁆ ∈ Y.Z 1 := by
    intro s hs a ha
    rcases hs with hs | hs
    · rw [Subgroup.commutator_comm] at hAV0
      exact hZ0Z1 (hAV0 (Subgroup.commutator_mem_commutator hs ha))
    · rw [Subgroup.commutator_comm] at hAV2
      exact hZ2Z1 (hAV2 (Subgroup.commutator_mem_commutator hs ha))
  have hdW : d ∈ Y.VNbr0 ⊔ Y.VNbr2 :=
    mem_VNbr0_sup_VNbr2_of_orderOf_three Y H hZ hd hd3
  have hzW : Subgroup.zpowers d ≤ Y.VNbr0 ⊔ Y.VNbr2 := Subgroup.zpowers_le.mpr hdW
  refine (Subgroup.commutator_mono le_rfl hzW).trans ?_
  rw [Subgroup.commutator_comm]
  have hmain := CFSG.Quasithin.D14.commutator_closure_le
    (S := ((Y.VNbr0 : Set G) ∪ (Y.VNbr2 : Set G)))
    (K := (Y.Q 0 ⊓ Y.Q 2 : Subgroup G)) (N := Y.Z 1) hSN hcomm
  simpa [Subgroup.sup_eq_closure] using hmain

private theorem finite_sup_zpowers_of_le_normalizer {A : Subgroup G} {d : G} [Finite ↥A]
    [Finite ↥(Subgroup.zpowers d)]
    (hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (A : Set G)) :
    Finite ↥(A ⊔ Subgroup.zpowers d) := by
  have hset : ((A ⊔ Subgroup.zpowers d : Subgroup G) : Set G) =
      (A : Set G) * (Subgroup.zpowers d : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers d) hdN
  refine Finite.of_surjective
    (fun p : ↥A × ↥(Subgroup.zpowers d) =>
      (⟨(p.1 : G) * (p.2 : G), ?_⟩ : ↥(A ⊔ Subgroup.zpowers d))) ?_
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  · rintro ⟨x, hx⟩
    have hx' : x ∈ ((A : Set G) * (Subgroup.zpowers d : Set G)) := by
      rw [← hset]; exact hx
    obtain ⟨y, hy, a, ha, hya⟩ := hx'
    exact ⟨(⟨y, hy⟩, ⟨a, ha⟩), Subtype.ext hya⟩

private theorem centralizer_subgroupOf_eq_of_le {R T : Subgroup G} (hRT : R ≤ T) :
    Subgroup.centralizer ((R.subgroupOf T : Subgroup ↥T) : Set ↥T) =
      (Subgroup.centralizer (R : Set G)).subgroupOf T := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hRT hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  · intro h r hr
    exact Subtype.ext (h (r : G) (Subgroup.mem_subgroupOf.mp hr))

theorem s52_A_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) {d : G}
    (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    Y.Q 0 ⊓ Y.Q 2 = (Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Y.Z 1 ∧
      Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G) ⊓ Y.Z 1 = ⊥ := by
  classical
  haveI hG0fin : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  haveI hQ0fin : Finite ↥(Y.Q 0) :=
    Finite.of_injective (Subgroup.inclusion (Y.Q_le_Gi 0))
      (Subgroup.inclusion_injective _)
  haveI hAfin : Finite ↥(Y.Q 0 ⊓ Y.Q 2) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  obtain ⟨-, -, -, -, hsup, -, -, -⟩ := Y.s52_step8 H hZ
  have hsupA : Y.Z 1 ≤ Y.Q 0 ⊓ Y.Q 2 := by
    refine le_inf (Z_one_le_Q_zero Y H hZ) ?_
    rw [hsup]
    exact sup_le (Z_zero_le_Q_two Y H hZ) (Y.Z_le_Q 2)
  set T : Subgroup G := (Y.Q 0 ⊓ Y.Q 2) ⊔ Subgroup.zpowers d with hT
  have hAT : Y.Q 0 ⊓ Y.Q 2 ≤ T := by rw [hT]; exact le_sup_left
  have hzpT : Subgroup.zpowers d ≤ T := by rw [hT]; exact le_sup_right
  have hZ1T : Y.Z 1 ≤ T := hsupA.trans hAT
  have hzpfin : Finite ↥(Subgroup.zpowers d) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hd3]; norm_num)
  have hzN : Subgroup.zpowers d ≤
      Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr ((s52_A_normal Y H hZ).1 hd)
  haveI hTfin : Finite ↥T := by
    rw [hT]
    exact finite_sup_zpowers_of_le_normalizer hzN
  have hcommG : ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), Subgroup.zpowers d⁆ ≤ Y.Z 1 :=
    commutator_A_zpowers_le_Z_one Y H hZ hd hd3
  have hcommT : ⁅(Y.Q 0 ⊓ Y.Q 2).subgroupOf T, (Subgroup.zpowers d).subgroupOf T⁆ ≤
      (Y.Z 1).subgroupOf T := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ Y.Q 0 ⊓ Y.Q 2 := Subgroup.mem_subgroupOf.mp hx
    have hr' : (r : G) ∈ Subgroup.zpowers d := Subgroup.mem_subgroupOf.mp hr
    change ⁅(x : G), (r : G)⁆ ∈ Y.Z 1
    exact hcommG (Subgroup.commutator_mem_commutator hx' hr')
  have hNX : (Y.Z 1).subgroupOf T ≤ (Y.Q 0 ⊓ Y.Q 2).subgroupOf T := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hsupA (Subgroup.mem_subgroupOf.mp hx))
  have hRX : (Subgroup.zpowers d).subgroupOf T ≤
      Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2).subgroupOf T : Set ↥T) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact hcommT.trans hNX
  have hRN : (Subgroup.zpowers d).subgroupOf T ≤
      Subgroup.normalizer ((Y.Z 1).subgroupOf T : Set ↥T) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_le]
    intro x hx r hr
    rw [Subgroup.mem_subgroupOf]
    have hxZ : (x : G) ∈ Y.Z 1 := Subgroup.mem_subgroupOf.mp hx
    have hr' : (r : G) ∈ Subgroup.zpowers d := Subgroup.mem_subgroupOf.mp hr
    have hrL : (r : G) ∈ Y.L 1 := (Subgroup.zpowers_le (H := Y.L 1)).mpr hd hr'
    have hnorm : conjSub (r : G) (Y.Z 1) = Y.Z 1 :=
      Y.Z_normal 1 (r : G) (Y.L_le_Gi 1 hrL)
    have hconj : (r : G) * (x : G)⁻¹ * (r : G)⁻¹ ∈ Y.Z 1 := by
      have h := mul_mem_conjSub (g := (r : G)) (H := Y.Z 1) ((Y.Z 1).inv_mem hxZ)
      rwa [hnorm] at h
    change ⁅(x : G), (r : G)⁆ ∈ Y.Z 1
    have hcomm : ⁅(x : G), (r : G)⁆ =
        (x : G) * ((r : G) * (x : G)⁻¹ * (r : G)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hcomm]
    exact (Y.Z 1).mul_mem hxZ hconj
  have hRcard : Nat.card ↥((Subgroup.zpowers d).subgroupOf T) = 3 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpT).toEquiv
    rw [h, Nat.card_zpowers, hd3]
  have hR3 : IsPGroup 3 ((Subgroup.zpowers d).subgroupOf T) :=
    IsPGroup.of_card (n := 1) (by rw [hRcard]; norm_num)
  have hNcard : Nat.card ↥((Y.Z 1).subgroupOf T) = 4 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1T).toEquiv
    rw [h, (Y.s52_step8_Z H hZ 1 (by norm_num)).2]
  have hN3 : ¬ 3 ∣ Nat.card ↥((Y.Z 1).subgroupOf T) := by
    rw [hNcard]; norm_num
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := (Y.Q 0 ⊓ Y.Q 2).subgroupOf T) (N := (Y.Z 1).subgroupOf T)
    (R := (Subgroup.zpowers d).subgroupOf T) hNX hRX hRN hR3 hN3 hcommT
  have hcent : Subgroup.centralizer (Subgroup.zpowers d : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCT : Subgroup.centralizer
        (((Subgroup.zpowers d).subgroupOf T : Subgroup ↥T) : Set ↥T) =
      (Subgroup.centralizer (Subgroup.zpowers d : Set G)).subgroupOf T :=
    centralizer_subgroupOf_eq_of_le hzpT
  have hsubOf : (Y.Q 0 ⊓ Y.Q 2).subgroupOf T ⊓
        (Subgroup.centralizer (Subgroup.zpowers d : Set G)).subgroupOf T =
      ((Y.Q 0 ⊓ Y.Q 2) ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G)).subgroupOf T := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hDsub : (Y.Q 0 ⊓ Y.Q 2) ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G) ≤ T :=
    inf_le_left.trans hAT
  have hmap := congrArg (Subgroup.map T.subtype) hcover
  rw [Subgroup.map_sup, hCT, hsubOf,
    Subgroup.map_subgroupOf_eq_of_le hDsub,
    Subgroup.map_subgroupOf_eq_of_le hZ1T,
    Subgroup.map_subgroupOf_eq_of_le hAT] at hmap
  rw [hcent] at hmap
  refine ⟨hmap.symm, ?_⟩
  have hC : Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ :=
    Z_one_inf_centralizer_eq_bot Y H hZ hd hd3
  refine le_bot_iff.mp ?_
  calc (Y.Q 0 ⊓ Y.Q 2) ⊓ Subgroup.centralizer ({d} : Set G) ⊓ Y.Z 1
      ≤ Subgroup.centralizer ({d} : Set G) ⊓ Y.Z 1 := inf_le_inf inf_le_right le_rfl
    _ = ⊥ := by rw [inf_comm, hC]

theorem centralZData (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.CentralZData := by
  obtain ⟨h1, h2, -, h4, -, -, hcard, -⟩ := Y.s52_step8 H hZ
  have hL0Z0 : Y.L 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G) :=
    Subgroup.le_centralizer_iff.mp (h1.le.trans inf_le_right)
  exact ⟨hcard, h2, hL0Z0, h4, Z_one_eq_iSup_conj Y H hZ h2 h4,
    (Y.s52_step8_Z H hZ 1 (by norm_num : Odd (1 : ℤ))).2, Z_one_le_Q_zero Y H hZ⟩

end Setup

end CFSG.Quasithin.St84

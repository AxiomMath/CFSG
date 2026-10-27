module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAV2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_not_Z_le_Qy_start
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    ¬ caseAZ (x b) ≤ CosetGeom.Qy (x 0) := by
  intro hZ
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hxb_type : CosetGeom.vtype (x b) = true :=
    (hx.vtype_eq_true_iff_even le_rfl).mpr hbe
  obtain ⟨y, hyZ, hyQb⟩ := SetLike.not_le_iff_exists.mp hx.not_le
  have hyQpred : y ∈ CosetGeom.Qy (x (b - 1)) :=
    hx.ball (x 0) (x (b - 1)) hx.type_two
      (le_of_eq (GPath.IsGeodesic.dist_eq hconn hx.geodesic (show b - 1 ≤ b by omega))) hyZ
  have hb1n : x (b - 1) ∈ CosetGeom.nbrs (x b) := by
    have h := x.adj (b - 1) (by omega)
    rw [Nat.sub_add_cancel (show 1 ≤ b by omega)] at h
    simpa [CosetGeom.nbrs] using h.symm
  have hyAS : y ∈ caseAS (x b) (x (b - 1)) := by
    have hb1n' : x b ∈ CosetGeom.nbrs (x (b - 1)) := CosetGeom.mem_nbrs_symm hb1n
    have h := caseA_Qy_le_caseAS hfr (v := x (b - 1)) (w := x b) hb1n' hyQpred
    rwa [caseAS_comm] at h
  have hcomm : ⁅caseAZ (x b), Subgroup.zpowers y⁆ = caseAZ (x (b - 1)) :=
    caseA_commutator_Z_zpowers hfr hxb_type hb1n hyAS hyQb
  have hbot : ⁅caseAZ (x b), Subgroup.zpowers y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hzy : Commute y z := caseA_Z_commute_Qy (x 0) hyZ (hZ hz)
    exact hzy.zpow_left n
  exact caseA_Z_ne_bot hfr (x (b - 1)) (by rw [← hcomm, hbot])

private theorem a2a_commutator_Z_eq_of_not_le
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {β α : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (hα : α ∈ CosetGeom.nbrs β)
    {B : Subgroup (f112Amalgam L1 L2 S).Ghat} (hB : B ≤ CosetGeom.Qy α)
    (hBnot : ¬ B ≤ CosetGeom.Qy β) :
    ⁅caseAZ β, B⁆ = caseAZ α := by
  obtain ⟨y, hyB, hyQβ⟩ := SetLike.not_le_iff_exists.mp hBnot
  have hαβ : β ∈ CosetGeom.nbrs α := CosetGeom.mem_nbrs_symm hα
  have hyAS : y ∈ caseAS β α := by
    have h := caseA_Qy_le_caseAS hfr hαβ (hB hyB)
    rwa [caseAS_comm] at h
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr fun z hz b hb => ?_
    by_cases hbQ : b ∈ CosetGeom.Qy β
    · have hzb : z * b = b * z := caseA_Z_commute_Qy β hz hbQ
      rw [show ⁅z, b⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr hzb]
      exact (caseAZ α).one_mem
    · have hbAS : b ∈ caseAS β α := by
        have h := caseA_Qy_le_caseAS hfr hαβ (hB hb)
        rwa [caseAS_comm] at h
      have hbcomm : ⁅caseAZ β, Subgroup.zpowers b⁆ = caseAZ α :=
        caseA_commutator_Z_zpowers hfr hβ hα hbAS hbQ
      have hmem : ⁅z, b⁆ ∈ ⁅caseAZ β, Subgroup.zpowers b⁆ :=
        Subgroup.commutator_mem_commutator hz (Subgroup.mem_zpowers b)
      rwa [hbcomm] at hmem
  · have hycomm : ⁅caseAZ β, Subgroup.zpowers y⁆ = caseAZ α :=
      caseA_commutator_Z_zpowers hfr hβ hα hyAS hyQβ
    calc caseAZ α = ⁅caseAZ β, Subgroup.zpowers y⁆ := hycomm.symm
      _ ≤ ⁅caseAZ β, B⁆ := Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr hyB)

theorem caseA_commutator_Z_start_end
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    ⁅caseAZ (x 0), caseAZ (x b)⁆ = caseAZ (x 1) := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hxb_type : CosetGeom.vtype (x b) = true :=
    (hx.vtype_eq_true_iff_even le_rfl).mpr hbe
  have hB_le : caseAZ (x b) ≤ CosetGeom.Qy (x 1) :=
    hx.ball (x b) (x 1) hxb_type (by
      have h := GPath.dist_le_sub hconn x (show 1 ≤ b by omega) (le_refl b)
      rw [CosetGeom.dist_comm]
      exact h)
  have hBnot : ¬ caseAZ (x b) ≤ CosetGeom.Qy (x 0) :=
    caseA_not_Z_le_Qy_start hfr hx hbe hb
  have hx1 : x 1 ∈ CosetGeom.nbrs (x 0) := by
    simpa [CosetGeom.nbrs] using x.adj 0 (by omega)
  exact a2a_commutator_Z_eq_of_not_le hfr hx.type_two hx1 hB_le hBnot

theorem caseA_Z_one_eq_Z_pred
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAZ (x 1) = caseAZ (x (b - 1)) := by
  have hleft : ⁅caseAZ (x 0), caseAZ (x b)⁆ = caseAZ (x 1) :=
    caseA_commutator_Z_start_end hfr hx hbe hb
  have hright : ⁅caseAZ (x b), caseAZ (x 0)⁆ = caseAZ (x (b - 1)) := by
    have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
    have hxb_type : CosetGeom.vtype (x b) = true :=
      (hx.vtype_eq_true_iff_even le_rfl).mpr hbe
    have hA_le : caseAZ (x 0) ≤ CosetGeom.Qy (x (b - 1)) :=
      hx.ball (x 0) (x (b - 1)) hx.type_two
        (le_of_eq (GPath.IsGeodesic.dist_eq hconn hx.geodesic (show b - 1 ≤ b by omega)))
    have hb1n : x (b - 1) ∈ CosetGeom.nbrs (x b) := by
      have h := x.adj (b - 1) (by omega)
      rw [Nat.sub_add_cancel (show 1 ≤ b by omega)] at h
      simpa [CosetGeom.nbrs] using h.symm
    exact a2a_commutator_Z_eq_of_not_le hfr hxb_type hb1n hA_le hx.not_le
  rw [Subgroup.commutator_comm] at hright
  exact hleft.symm.trans hright

theorem caseA_critPath_reverse
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseACritPath L1 L2 S b x.rev := by
  have hxb_type : CosetGeom.vtype (x b) = true :=
    (hx.vtype_eq_true_iff_even le_rfl).mpr hbe
  refine ⟨GPath.IsGeodesic.rev hx.geodesic, ?_, hx.ball, ?_⟩
  · rw [GPath.rev_apply x (Nat.zero_le b), Nat.sub_zero]
    exact hxb_type
  · rw [GPath.rev_apply x (Nat.zero_le b), GPath.rev_apply x le_rfl, Nat.sub_zero, Nat.sub_self]
    exact caseA_not_Z_le_Qy_start hfr hx hbe hb

theorem caseA_stab_inf_le_stab
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    CosetGeom.stab (x 1) ⊓ CosetGeom.stab (x (b - 2)) ≤ CosetGeom.stab (x (b - 1)) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hg1, hgb2⟩ := hg
  obtain ⟨hG1, hfix1⟩ := CosetGeom.mem_stab.mp hg1
  obtain ⟨hGb2, hfixb2⟩ := CosetGeom.mem_stab.mp hgb2
  set u : f112Acting L1 L2 S := ⟨g, hG1⟩ with hu
  have hfixb2' : u • x (b - 2) = x (b - 2) := by
    rw [hu]; exact hfixb2
  have hβ : CosetGeom.vtype (x (b - 2)) = true :=
    (hx.vtype_eq_true_iff_even (i := b - 2) (by omega)).mpr
      (by obtain ⟨k, rfl⟩ := hbe; exact ⟨k - 1, by omega⟩)
  have hβadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
    have := x.adj (b - 2) (by omega)
    rwa [show b - 2 + 1 = b - 1 by omega] at this
  have hnewadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (u • x (b - 1)) := by
    have := (CosetGeom.smul_adj u).mpr hβadj
    rwa [hfixb2'] at this
  have hZ1pred : caseAZ (x 1) = caseAZ (x (b - 1)) :=
    caseA_Z_one_eq_Z_pred hfr hx hbe hb
  have hconj1 : caseAZ (x 1) = conjSub (u : (f112Amalgam L1 L2 S).Ghat) (caseAZ (x 1)) := by
    have := caseA_Z_smul u (x 1)
    rw [hfix1] at this
    exact this
  have hZeq : caseAZ (u • x (b - 1)) = caseAZ (x (b - 1)) := by
    rw [caseA_Z_smul u (x (b - 1)), ← hZ1pred, ← hconj1]
  have hsmul : u • x (b - 1) = x (b - 1) := by
    by_contra hne
    have hbot : caseAZ (x (b - 1)) = ⊥ := by
      have h := caseA_Z_inf_Z_eq_bot hfr hβ hnewadj hβadj hne
      simpa [hZeq] using h
    exact caseA_Z_ne_bot hfr (x (b - 1)) hbot
  exact CosetGeom.mem_stab_of_smul_eq (g := u) hsmul

private theorem a2b_Z_le_Qy_pred
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b)
    {u : f112Gamma L1 L2 S} (hu : CosetGeom.vtype u = true)
    (hdu : CosetGeom.dist u (x 1) ≤ 3) :
    caseAZ u ≤ CosetGeom.Qy (x (b - 2)) := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  by_cases hle : CosetGeom.dist u (x (b - 2)) ≤ b - 1
  · exact hx.ball u (x (b - 2)) hu hle
  · intro z hz
    have hzQ1 : z ∈ CosetGeom.Qy (x 1) := hx.ball u (x 1) hu (by omega) hz
    have hzQb3 : z ∈ CosetGeom.Qy (x (b - 3)) := by
      refine hx.ball u (x (b - 3)) hu ?_ hz
      have htri : CosetGeom.dist u (x (b - 3)) ≤
          CosetGeom.dist u (x 1) + CosetGeom.dist (x 1) (x (b - 3)) := hconn.dist_triangle
      have hdx : CosetGeom.dist (x 1) (x (b - 3)) ≤ b - 4 :=
        GPath.dist_le_sub hconn x (i := 1) (j := b - 3) (by omega) (by omega)
      omega
    have hzstab1 : z ∈ CosetGeom.stab (x 1) := caseA_Qy_le_stab (x 1) hzQ1
    have hadj32 : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 3)) (x (b - 2)) := by
      have := x.adj (b - 3) (by omega)
      rwa [show b - 3 + 1 = b - 2 by omega] at this
    have hzstabb2 : z ∈ CosetGeom.stab (x (b - 2)) := by
      have hzK : z ∈ CosetGeom.ballStab 1 (x (b - 3)) :=
        caseA_Qy_le_ballStab_one hfr (x (b - 3)) hzQb3
      have hd : CosetGeom.dist (x (b - 3)) (x (b - 2)) ≤ 1 :=
        (CosetGeom.dist_eq_one_iff_adj.mpr hadj32).le
      exact CosetGeom.ballStab_le_stab_of_dist_le hd hzK
    have hzstabb1 : z ∈ CosetGeom.stab (x (b - 1)) :=
      caseA_stab_inf_le_stab hfr hx hbe hb (Subgroup.mem_inf.mpr ⟨hzstab1, hzstabb2⟩)
    have hzstabb3 : z ∈ CosetGeom.stab (x (b - 3)) := caseA_Qy_le_stab (x (b - 3)) hzQb3
    have h2 : ∃ k, orderOf z = 2 ^ k := by
      have hz2 : z * z = 1 := by
        simpa [pow_two] using CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hz
      have hdvd : orderOf z ∣ 2 ^ 1 := by
        rw [pow_one]
        exact orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨k, hk⟩
    have hadj12 : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1)) := by
      have := x.adj (b - 2) (by omega)
      rwa [show b - 2 + 1 = b - 1 by omega] at this
    have hne : x (b - 3) ≠ x (b - 1) := by
      have hNB : x.NoBack := GPath.noBack_of_dist_eq hconn x hx.geodesic
      have := hNB (b - 3) (by omega)
      rwa [show b - 3 + 2 = b - 1 by omega] at this
    exact caseA_mem_Qy_of_fixes_two_nbrs hfr hadj32.symm hadj12 hne
      hzstabb2 hzstabb3 hzstabb1 h2

theorem caseA_N_le_Qy
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAN (x 1) ≤ CosetGeom.Qy (x (b - 2)) := by
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  unfold caseAN
  refine iSup₂_le fun w hw => ?_
  unfold caseAX
  refine iSup₂_le fun u hu => ?_
  have hw2 : Even (CosetGeom.dist (x 1) w) := by rw [hw]; norm_num
  have hx1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hwv : CosetGeom.vtype w = false := by
    have h := (CosetGeom.vtype_eq_iff_even_dist rfl (x 1) w).mpr hw2
    rw [hx1] at h
    exact h.symm
  have huv : CosetGeom.vtype u = true := by
    have hne := CosetGeom.vtype_ne_of_adj hu
    rw [hwv] at hne
    cases h : CosetGeom.vtype u <;> simp_all
  have hdu : CosetGeom.dist u (x 1) ≤ 3 := by
    have htri : CosetGeom.dist u (x 1) ≤ CosetGeom.dist u w + CosetGeom.dist w (x 1) :=
      hconn.dist_triangle
    have h1 : CosetGeom.dist u w = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hu.symm
    have h2 : CosetGeom.dist w (x 1) = 2 := by rw [CosetGeom.dist_comm]; exact hw
    omega
  exact a2b_Z_le_Qy_pred hfr hx hbe hb huv hdu

theorem caseA_N_le_Qy_symm
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAN (x (b - 1)) ≤ CosetGeom.Qy (x 2) := by
  have hx' : caseACritPath L1 L2 S b x.rev := caseA_critPath_reverse hfr hx hbe hb
  have h := caseA_N_le_Qy hfr hx' hbe hb
  have h1 : x.rev 1 = x (b - 1) := by
    rw [GPath.rev_apply (hi := by omega)]
  have h2 : x.rev (b - 2) = x 2 := by
    rw [GPath.rev_apply (hi := by omega)]
    congr 1
    omega
  rwa [h1, h2] at h

end CFSG.Quasithin.Stroth

end

module

public import Certificates.Kernel.D42.CGlue
public import Certificates.Kernel.D42.ClassGlue
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8

public section

namespace CFSG.KD.D42

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.Q3.O8 CFSG.ClassicalInvolution.O8Data
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42

theorem hn32 : (360 : ℕ) < 2 ^ 32 := by norm_num

section Model


theorem main_rep_idx {j : ℕ} : CFSG.Monster.B.Co2.Rep 360 (mainArrs.getD (mainIdx j) #[])
    (mainPerm (mainIdx j)) := by
  unfold mainIdx
  split_ifs
  · exact main_rep (i := 0) (by norm_num)
  · exact main_rep (i := 2) (by norm_num)

theorem rep_zTbl {j : ℕ} : CFSG.Sporadic.Th.Rep 360 (zTbl j) (mainPerm (mainIdx j)) :=
  rep_arrTable hn32 main_rep_idx

theorem pGens_spec {j : ℕ} (h : sylowCheck j = true) :
    ∀ g ∈ pGens j, permOK 360 g = true ∧ invOK 360 g (invT 360 g) = true ∧
      tp 360 g ∈ autT ∧ tp 360 g * mainPerm (mainIdx j) = mainPerm (mainIdx j) * tp 360 g := by
  simp only [sylowCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hw, hg⟩, -⟩ := h
  intro g hgm
  obtain ⟨⟨hp, hi⟩, hc⟩ := hg g hgm
  obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hgm
  have hspec := autW_spec (hw w hwm)
  have heq : tp 360 (arrTable 360 (autW w)) = permOfArr 360 (autW w) :=
    rep_unique (rep_tp hp) (rep_arrTable hn32 hspec.1)
  refine ⟨hp, hi, heq ▸ hspec.2, ?_⟩
  exact (commTT_iff (rep_tp hp) rep_zTbl).1 hc

theorem pSub_spec {j : ℕ} (h : sylowCheck j = true) :
    genOf 360 (pGens j) ≤ centralizerIn autT (mainPerm (mainIdx j)) ∧
      Nat.card (genOf 360 (pGens j)) = pOrder j := by
  have hg := pGens_spec h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, hgm, rfl⟩
    have hgm' : g ∈ pGens j := by simpa using hgm
    obtain ⟨-, -, hA, hc⟩ := hg g hgm'
    exact mem_centralizerIn.2 ⟨hA, hc⟩
  · simp only [sylowCheck, Bool.and_eq_true] at h
    exact (enumOK_spec hn32 (fun g hgm => (hg g hgm).1) h.2).1

theorem mem_omegaT_of_siftOmega {T : Table} {g : Equiv.Perm (Fin 360)}
    (hT : CFSG.Sporadic.Th.Rep 360 T g) (h : siftOmega omegaLevels T = true) : g ∈ omegaT := by
  have hG : CFSG.Monster.B.Co2.Rep 360 (natArr T) g := co2Rep_natArr_iff.2 hT
  rw [omegaT, omegaQ, ← ofArrays_mem_iff (by norm_num) omegaChain_ok.1 hG]
  exact h

theorem uGens_spec {j : ℕ} (h : uCheck j = true) :
    ∀ g ∈ uGens j, permOK 360 g = true ∧ tp 360 g ∈ omegaT ∧
      tp 360 g * mainPerm (mainIdx j) = mainPerm (mainIdx j) * tp 360 g := by
  simp only [uCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hg, -⟩, -⟩ := h
  intro g hgm
  obtain ⟨⟨hp, hs⟩, hc⟩ := hg g hgm
  exact ⟨hp, mem_omegaT_of_siftOmega (rep_tp hp) hs, (commTT_iff (rep_tp hp) rep_zTbl).1 hc⟩

theorem uSub_spec {j : ℕ} (hP : sylowCheck j = true) (h : uCheck j = true) :
    genOf 360 (uGens j) ≤ omegaT ∧
      genOf 360 (uGens j) ≤ Subgroup.centralizer ({mainPerm (mainIdx j)} : Set _) ∧
      Nat.card (genOf 360 (uGens j)) = 512 ∧
      genOf 360 (pGens j) ≤ Subgroup.normalizer (genOf 360 (uGens j) : Set (Equiv.Perm (Fin 360))) := by
  have hg := uGens_spec h
  have hpg := pGens_spec hP
  have h' := h
  simp only [uCheck, Bool.and_eq_true] at h'
  obtain ⟨⟨-, henum⟩, hnorm⟩ := h'
  refine ⟨?_, ?_, (enumOK_spec hn32 (fun g hgm => (hg g hgm).1) henum).1, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, hgm, rfl⟩
    exact (hg g (by simpa using hgm)).2.1
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, hgm, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hg g (by simpa using hgm)).2.2
  · exact normOK_spec hn32 (fun g hgm => (hg g hgm).1) henum
      (fun c hcm => ⟨(hpg c hcm).1, (hpg c hcm).2.1⟩) hnorm

theorem sub_facts {j : ℕ} (hj : j < 2) : ∃ P U : Subgroup (Equiv.Perm (Fin 360)),
    P ≤ centralizerIn autT (mainPerm (mainIdx j)) ∧
    Nat.card P = pOrder j ∧ IsPGroup 2 U ∧ U ≤ omegaT ∧
    U ≤ Subgroup.centralizer ({mainPerm (mainIdx j)} : Set (Equiv.Perm (Fin 360))) ∧
    P ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 360))) ∧
    ∀ y ∈ P, y ≠ 1 → 9 ≤ Nat.card ↥⁅U, Subgroup.zpowers y⁆ := by
  have hs : sylowCheck j = true := by
    interval_cases j
    exacts [sylowCheck_k0, sylowCheck_k1]
  have hu : uCheck j = true := by
    interval_cases j
    exacts [uCheck_k0, uCheck_k1]
  have hc : ∀ y ∈ genOf 360 (pGens j), y ≠ 1 →
      9 ≤ Nat.card ↥⁅genOf 360 (uGens j), Subgroup.zpowers y⁆ := by
    interval_cases j
    exacts [comm_k0, comm_k1]
  obtain ⟨hPC, hPcard⟩ := pSub_spec hs
  obtain ⟨hUO, hUC, hUcard, hPN⟩ := uSub_spec hs hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨_, _, hPC, hPcard, IsPGroup.of_card (n := 9) (by rw [hUcard]; norm_num), hUO, hUC, hPN, hc⟩

theorem proof118001 :
    3 * (CFSG.Sporadic.Schreier.conjClass omegaT (mainPerm 1)).ncard ≤
        (CFSG.Sporadic.Schreier.conjClass autT (mainPerm 1)).ncard ∧
      ∀ j < 2, ∃ P U : Subgroup (Equiv.Perm (Fin 360)),
        P ≤ CFSG.Sporadic.Schreier.centralizerIn autT (mainPerm (mainIdx j)) ∧
        Nat.card P = pOrder j ∧ IsPGroup 2 U ∧ U ≤ omegaT ∧
        U ≤ Subgroup.centralizer ({mainPerm (mainIdx j)} : Set (Equiv.Perm (Fin 360))) ∧
        P ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 360))) ∧
        ∀ y ∈ P, y ≠ 1 → 9 ≤ Nat.card ↥⁅U, Subgroup.zpowers y⁆ :=
  ⟨CertificateChecks.KernelD42.three_mul_ncard_le, fun _ hj => sub_facts hj⟩

end Model

end CFSG.KD.D42

end

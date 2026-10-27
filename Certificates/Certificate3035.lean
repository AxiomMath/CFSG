module

public import Certificates.Kernel.MonsterB.IndOrbGlue

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.IndOrb CFSG.KC.U6Orb
  CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbChecks
  CertificateChecks.KernelMonB.IndOrbGlue

namespace CertificateChecks.Batch3035

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.IndOrb CFSG.KC.U6Orb
  CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbChecks
  CertificateChecks.KernelMonB.IndOrbGlue

set_option maxRecDepth 100000

theorem wCert_ok_0 :
    ∀ s ∈ [0, 1, 3, 7], natCertOK linW 2 (fun u => decide (u < 1024)) s (wCert s) = true := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact (wBfs kW0 (by norm_num) (by norm_num) (by norm_num)).2
  · exact (wBfs kW1 (by norm_num) (by norm_num) (by norm_num)).2
  · exact (wBfs kW3 (by norm_num) (by norm_num) (by norm_num)).2
  · exact (wBfs kW7 (by norm_num) (by norm_num) (by norm_num)).2

theorem wCert_size_1 :
    (wCert 0).pts.size = 1 ∧ (wCert 1).pts.size = 22 ∧
    (wCert 3).pts.size = 231 ∧ (wCert 7).pts.size = 770 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [size_of_toList w0, size_of_toList w1, size_of_toList w3, size_of_toList w7,
      orbL_length]

theorem wCert_sorted_2 :
    ((wCert 0).pts.toList ++ (wCert 1).pts.toList ++ (wCert 3).pts.toList ++
    (wCert 7).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 1024 := by
  rw [w0, w1, w3, w7, orbL_append, orbL_append, orbL_append, ← mergeSort_range]
  exact mergeSort_eq_of_perm (orbL_perm kWInv)

theorem zCert_ok_3 :
    ∀ s ∈ [0, 24, 1], natCertOK zAct 2 (fun n => decide (n < 2464)) s (zCert s) = true := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (zBfs kZ0 (by norm_num) (by norm_num) (by norm_num)).2
  · exact (zBfs kZ24 (by norm_num) (by norm_num) (by norm_num)).2
  · exact (zBfs kZ1 (by norm_num) (by norm_num) (by norm_num)).2

theorem zCert_size_4 :
    (zCert 0).pts.size = 462 ∧ (zCert 24).pts.size = 770 ∧ (zCert 1).pts.size = 1232 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [size_of_toList z0, size_of_toList z24, size_of_toList z1, orbL_length]

theorem zCert_sorted_5 :
    ((zCert 0).pts.toList ++ (zCert 24).pts.toList ++
    (zCert 1).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 2464 := by
  rw [z0, z24, z1, orbL_append, orbL_append, ← mergeSort_range]
  exact mergeSort_eq_of_perm (orbL_perm kZInv)

theorem fix_of {L : List (List ℕ)} {m b u : ℕ} (hL : L.length = m)
    (hw : ∀ k < m, (wordT (IG.F 0) (IG.F 1) (L[k]!) (b + u) = b + u))
    (h : ∃ wd ∈ L, wordT (IG.F 0) (IG.F 1) wd (b + u) ≠ b + u) : False := by
  obtain ⟨wd, hwd, hne⟩ := h
  obtain ⟨k, hk, rfl⟩ := mem_getElem! hwd
  exact hne (hw k (hL ▸ hk))

theorem sFix_W_8 :
    ∀ u ∈ (wCert 7).pts.toList, (∀ k < 4, (sArrs[k]!)[22 + u]! = 22 + u) → u = 7 := by
  intro u hu hfix
  rw [w7] at hu
  have hu' := hu
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hu
  have hlt := lt_of_mem_w (by norm_num) hu'
  rcases fixOK_sound kFixW j hj with h | h
  · simpa using h
  · exact (fix_of (m := 4) rfl (fun k hk => by rw [← sArrs_word hk (by omega)]; exact hfix k hk)
      h).elim

theorem sFix_Z_9 :
    ∀ n ∈ (zCert 24).pts.toList, (∀ k < 4, (sArrs[k]!)[1046 + n]! = 1046 + n) → n = 24 := by
  intro n hn hfix
  rw [z24] at hn
  have hn' := hn
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hn
  have hlt := lt_of_mem_z (by norm_num) hn'
  rcases fixOK_sound kFixZ j hj with h | h
  · simpa using h
  · exact (fix_of (m := 4) rfl (fun k hk => by rw [← sArrs_word hk (by omega)]; exact hfix k hk)
      h).elim

theorem s2Fix_Z_11 :
    ∀ n ∈ (zCert 1).pts.toList,
      (∀ k < 3, (s2Arrs[k]!)[1046 + n]! = 1046 + n) → n = 1 ∨ n = 277 := by
  intro n hn hfix
  rw [z1] at hn
  have hn' := hn
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hn
  have hlt := lt_of_mem_z (by norm_num) hn'
  rcases fixOK_sound kFix2Z j hj with h | h
  · simpa using h
  · exact (fix_of (m := 3) rfl (fun k hk => by rw [← s2Arrs_word hk (by omega)]; exact hfix k hk)
      h).elim

theorem sFix_7 : ∀ k < 4, (sArrs[k]!)[22 + 7]! = 22 + 7 := by
  intro k hk
  rw [sArrs_word hk (by norm_num)]
  obtain ⟨wd, hwd, rfl⟩ : ∃ wd ∈ sW, sW[k]! = wd :=
    ⟨_, by rw [getElem!_pos sW k (by simpa [sW] using hk)]; exact List.getElem_mem _, rfl⟩
  exact fixAt_sound kFix _ hwd

theorem s2Fix_10 : ∀ k < 3, (s2Arrs[k]!)[1046 + 1]! = 1046 + 1 := by
  intro k hk
  rw [s2Arrs_word hk (by norm_num)]
  obtain ⟨wd, hwd, rfl⟩ : ∃ wd ∈ s2W, s2W[k]! = wd :=
    ⟨_, by rw [getElem!_pos s2W k (by simpa [s2W] using hk)]; exact List.getElem_mem _, rfl⟩
  exact fixAt_sound kFix2 _ hwd

theorem indSigma_spec_14 :
    ∀ p ∈ indSigma, p.1 ∈ (wCert 7).pts.toList ∧ sigmaFun p.1 = p.2 := by
  intro p hp
  rw [indSigma_eq] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  rw [w7]
  exact ⟨(sig_key.1 i (List.mem_range.1 hi)).1, (sig_key.1 i (List.mem_range.1 hi)).2.1⟩

theorem indTau_spec_15 : ∀ p ∈ indTau, p.1 ∈ (zCert 1).pts.toList ∧ tauFun p.1 = p.2 := by
  intro p hp
  rw [indTau_eq] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  rw [z1]
  exact ⟨(tau_key.1 i (List.mem_range.1 hi)).1, (tau_key.1 i (List.mem_range.1 hi)).2.1⟩

theorem sigma_check_16 :
    sigmaFun 7 = 24 ∧ (∀ u ∈ (wCert 7).pts.toList,
    sigmaFun u ∈ (zCert 24).pts.toList ∧ ∀ g < 2, sigmaFun (linW g u) = zAct g (sigmaFun u)) ∧
    ∀ u ∈ (wCert 7).pts.toList, ∀ u' ∈ (wCert 7).pts.toList,
      sigmaFun u = sigmaFun u' → u = u' := by
  have hS := sigOK_sound kSig
  have hP := kPts
  simp only [Bool.and_eq_true, Nat.beq_eq] at hP
  have h7 : 7 ∈ wL 254 770 := orbOK_root kW7 (by norm_num)
  rw [w7, z24]
  refine ⟨by rw [sigma_tab h7, hP.1], fun u hu => ?_, fun u hu u' hu' e => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hu
    obtain ⟨h1, -, h3⟩ := hS j hj
    rw [sigma_tab hu]
    refine ⟨mem_z24.2 h1, fun g hg => ?_⟩
    have he := (orbOK_sound kW7).2.1 j hj g hg
    rw [← he.2, sigma_tab (mem_orbL.2 ⟨_, he.1, rfl⟩), h3 g hg,
      zAct_eq hg (inOrb_iff.1 h1).1]
  · obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hu
    obtain ⟨j', hj', rfl⟩ := mem_orbL.1 hu'
    rw [sigma_tab hu, sigma_tab hu'] at e
    rw [← (hS j hj).2.1, ← (hS j' hj').2.1, e]

theorem tau_check_17 :
    tauFun 1 = 277 ∧ ∀ n ∈ (zCert 1).pts.toList,
    tauFun n ∈ (zCert 1).pts.toList ∧ tauFun (tauFun n) = n ∧ tauFun n ≠ n ∧
      ∀ g < 2, tauFun (zAct g n) = zAct g (tauFun n) := by
  have hT := tauOK_sound kTau
  have hP := kPts
  simp only [Bool.and_eq_true, Nat.beq_eq] at hP
  have h1 : 1 ∈ zL 1232 1232 := orbOK_root kZ1 (by norm_num)
  rw [z1]
  refine ⟨by rw [tau_tab h1, hP.2], fun n hn => ?_⟩
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hn
  obtain ⟨t1, t2, t3, t4⟩ := hT j hj
  have ht := mem_z1.2 t1
  have hlt := lt_of_mem_z (by norm_num) hn
  refine ⟨by rw [tau_tab hn]; exact ht, by rw [tau_tab hn, tau_tab ht, t2],
    by rw [tau_tab hn]; exact t3, fun g hg => ?_⟩
  have he := (orbOK_sound kZ1).2.1 j hj g hg
  have hz : zAct g (fget (IZ 0) (1232 + j) 12) ∈ zL 1232 1232 := by
    have e2 : fget (IZ 0) (1232 + tabE 2 12 (IZ 4) j g) 12 =
        zActK (IG.F 0) (IG.F 1) 1046 g (fget (IZ 0) (1232 + j) 12) := he.2
    rw [← zAct_eq hg hlt, ← e2]
    exact mem_orbL.2 ⟨_, he.1, rfl⟩
  rw [tau_tab hz, tau_tab hn, ← zAct_eq hg hlt, t4 g hg,
    zAct_eq hg (inOrb_iff.1 t1).1]

theorem indSigma_graph_18 : ∀ u ∈ (wCert 7).pts.toList, (u, sigmaFun u) ∈ indSigma := by
  intro u hu
  rw [w7] at hu
  obtain ⟨i, hi, rfl⟩ := sig_key.2 u hu
  rw [(sig_key.1 i hi).2.1, indSigma_eq]
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem indTau_graph_19 : ∀ n ∈ (zCert 1).pts.toList, (n, tauFun n) ∈ indTau := by
  intro n hn
  rw [z1] at hn
  obtain ⟨i, hi, rfl⟩ := tau_key.2 n hn
  rw [(tau_key.1 i hi).2.1, indTau_eq]
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem hexMask_lt_20 :
    ∀ i < 76,
    hexMask ((hexCat (hCat i)).map jEmb) < hexMask ((hexCat (hCat (i + 1))).map jEmb) := by
  decide +kernel

end CertificateChecks.Batch3035

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer in
theorem certificate3035 : (∀ s ∈ [0, 1, 3, 7],
       natCertOK linW 2 (fun u => decide (u < 1024)) s (wCert s) = true)
    ∧ ((wCert 0).pts.size = 1 ∧ (wCert 1).pts.size = 22 ∧
       (wCert 3).pts.size = 231 ∧ (wCert 7).pts.size = 770)
    ∧ (((wCert 0).pts.toList ++ (wCert 1).pts.toList ++ (wCert 3).pts.toList ++
       (wCert 7).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 1024)
    ∧ (∀ s ∈ [0, 24, 1],
       natCertOK zAct 2 (fun n => decide (n < 2464)) s (zCert s) = true)
    ∧ ((zCert 0).pts.size = 462 ∧ (zCert 24).pts.size = 770 ∧
       (zCert 1).pts.size = 1232)
    ∧ (((zCert 0).pts.toList ++ (zCert 24).pts.toList ++
       (zCert 1).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 2464)
    ∧ (∀ g < 2, ∀ n < 2464,
       1046 ≤ (indAB g)[1046 + n]! ∧ (indAB g)[1046 + n]! < 3510)
    ∧ (∀ k < 4, (sArrs[k]!)[22 + 7]! = 22 + 7)
    ∧ (∀ u ∈ (wCert 7).pts.toList,
       (∀ k < 4, (sArrs[k]!)[22 + u]! = 22 + u) → u = 7)
    ∧ (∀ n ∈ (zCert 24).pts.toList,
       (∀ k < 4, (sArrs[k]!)[1046 + n]! = 1046 + n) → n = 24)
    ∧ (∀ k < 3, (s2Arrs[k]!)[1046 + 1]! = 1046 + 1)
    ∧ (∀ n ∈ (zCert 1).pts.toList,
       (∀ k < 3, (s2Arrs[k]!)[1046 + n]! = 1046 + n) → n = 1 ∨ n = 277)
    ∧ (∀ k < 4, (sArrs[k]!).size = 3510)
    ∧ (∀ k < 3, (s2Arrs[k]!).size = 3510)
    ∧ (∀ p ∈ indSigma, p.1 ∈ (wCert 7).pts.toList ∧ sigmaFun p.1 = p.2)
    ∧ (∀ p ∈ indTau, p.1 ∈ (zCert 1).pts.toList ∧ tauFun p.1 = p.2)
    ∧ (sigmaFun 7 = 24 ∧ (∀ u ∈ (wCert 7).pts.toList,
       sigmaFun u ∈ (zCert 24).pts.toList ∧ ∀ g < 2, sigmaFun (linW g u) = zAct g (sigmaFun u)) ∧
       ∀ u ∈ (wCert 7).pts.toList, ∀ u' ∈ (wCert 7).pts.toList,
         sigmaFun u = sigmaFun u' → u = u')
    ∧ (tauFun 1 = 277 ∧ ∀ n ∈ (zCert 1).pts.toList,
       tauFun n ∈ (zCert 1).pts.toList ∧ tauFun (tauFun n) = n ∧ tauFun n ≠ n ∧
         ∀ g < 2, tauFun (zAct g n) = zAct g (tauFun n))
    ∧ (∀ u ∈ (wCert 7).pts.toList, (u, sigmaFun u) ∈ indSigma)
    ∧ (∀ n ∈ (zCert 1).pts.toList, (n, tauFun n) ∈ indTau)
    ∧ (∀ i < 76,
       hexMask ((hexCat (hCat i)).map jEmb) < hexMask ((hexCat (hCat (i + 1))).map jEmb)) := by
  exact ⟨CertificateChecks.Batch3035.wCert_ok_0, CertificateChecks.Batch3035.wCert_size_1, CertificateChecks.Batch3035.wCert_sorted_2,
    CertificateChecks.Batch3035.zCert_ok_3, CertificateChecks.Batch3035.zCert_size_4, CertificateChecks.Batch3035.zCert_sorted_5, zAct_range',
    CertificateChecks.Batch3035.sFix_7, CertificateChecks.Batch3035.sFix_W_8, CertificateChecks.Batch3035.sFix_Z_9, CertificateChecks.Batch3035.s2Fix_10,
    CertificateChecks.Batch3035.s2Fix_Z_11, sArrs_size', s2Arrs_size', CertificateChecks.Batch3035.indSigma_spec_14,
    CertificateChecks.Batch3035.indTau_spec_15, CertificateChecks.Batch3035.sigma_check_16, CertificateChecks.Batch3035.tau_check_17,
    CertificateChecks.Batch3035.indSigma_graph_18, CertificateChecks.Batch3035.indTau_graph_19, CertificateChecks.Batch3035.hexMask_lt_20⟩

end Certificates

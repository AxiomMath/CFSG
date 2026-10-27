module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagA2A1Calc
public import CFSG.LocalAnalysis.StandardType.PhanELocalPlane

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem exists_psiA2A1 (hK : Nat.card K = (2 ^ f) ^ 2) {c : FlagK K 3 × FlagK K 2}
    (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    ∃ c' : FlagK K 3 × FlagK K 2, c'.1 ∈ refSet K 3 [0, 1, 3] ∧
      c'.1.E 2 = Vsub 3 1 ⊔ Submodule.span K (jShift21 K f '' (c.2.E 1 : Set (Fin 2 → K))) ∧
      c'.2.E 1 = Submodule.span K (jShift21Inv K f '' (c.1.E 2 : Set (Fin 3 → K))) := by
  have hV1 : c.1.E 1 = Vsub 3 1 := hc 1 (by decide)
  have hVM : Vsub 3 1 ≤ c.1.E 2 := by rw [← hV1]; exact c.1.mono (by norm_num)
  have hMfin : finrank K (c.1.E 2) = 2 := c.1.dim 2 (by norm_num)
  have hLfin : finrank K (c.2.E 1) = 1 := c.2.dim 1 (by norm_num)
  have hVfin : finrank K (Vsub 3 1) = 1 :=
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)
  let W := Vsub 3 1 ⊔ Submodule.span K (jShift21 K f '' (c.2.E 1 : Set (Fin 2 → K)))
  have hWfin : finrank K W = 2 := by
    change finrank K ↥(Vsub 3 1 ⊔
      Submodule.span K (jShift21 K f '' (c.2.E 1 : Set (Fin 2 → K)))) = 2
    exact q2cFA2_finrank_sup_jShift21_span hLfin
  let c1 : FlagK K 3 := Plane.ofChain (Vsub 3 1) W hVfin hWfin le_sup_left
  have hc1E1 : c1.E 1 = Vsub 3 1 := Plane.ofChain_E_one (Vsub 3 1) W hVfin hWfin le_sup_left
  have hc1E2 : c1.E 2 = W := Plane.ofChain_E_two (Vsub 3 1) W hVfin hWfin le_sup_left
  let M := c.1.E 2
  have hβfin : finrank K (Submodule.span K (jShift21Inv K f '' (M : Set (Fin 3 → K)))) = 1 := by
    change finrank K (Submodule.span K
      (jShift21Inv K f '' (c.1.E 2 : Set (Fin 3 → K)))) = 1
    exact q2cFA2_finrank_jShift21Inv_span hK hVM hMfin
  let c2 : FlagK K 2 :=
    Exch.ofPoint (Submodule.span K (jShift21Inv K f '' (M : Set (Fin 3 → K)))) hβfin
  have hc2E1 : c2.E 1 = Submodule.span K (jShift21Inv K f '' (M : Set (Fin 3 → K))) :=
    Exch.ofPoint_E_one (Submodule.span K (jShift21Inv K f '' (M : Set (Fin 3 → K)))) hβfin
  refine ⟨(c1, c2), ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < 3 := by simpa using hi
    interval_cases i
    · show c1.E 0 = Vsub 3 0
      rw [FlagK.E_zero, Vsub_zero]
    · show c1.E 1 = Vsub 3 1
      rw [hc1E1]
    · show c1.E 3 = Vsub 3 3
      rw [c1.top 3 (by norm_num), Vsub_self]
  · exact hc1E2
  · exact hc2E1

@[expose] noncomputable def psiA2A1 (hK : Nat.card K = (2 ^ f) ^ 2)
    (c : FlagK K 3 × FlagK K 2) : FlagK K 3 × FlagK K 2 :=
  open Classical in
  if h : c.1 ∈ refSet K 3 [0, 1, 3] then Classical.choose (exists_psiA2A1 hK h) else c

private theorem q2cFA2_psi_mem (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).1 ∈ refSet K 3 [0, 1, 3] := by
  unfold psiA2A1
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_psiA2A1 hK hc)).1

private theorem q2cFA2_psi_fst_E_two (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).1.E 2 = Exch.dirZ K f (c.2.E 1) := by
  unfold psiA2A1
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_psiA2A1 hK hc)).2.1

private theorem q2cFA2_psi_snd_E_one (hK : Nat.card K = (2 ^ f) ^ 2)
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    (psiA2A1 hK c).2.E 1 =
      Submodule.span K (jShift21Inv K f '' (c.1.E 2 : Set (Fin 3 → K))) := by
  unfold psiA2A1
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_psiA2A1 hK hc)).2.2

private theorem q2cFA2_opp_psi (hK : Nat.card K = (2 ^ f) ^ 2) {E : FlagK K 3}
    (hfar : E ∈ farSet 3 [0, 1, 3]) {z : FlagK K 2}
    (hbu : E.E 1 ⊔ Vsub 3 1 ≠ Exch.dirZ K f (z.E 1)) {F : FlagK K 3}
    (hF : F ∈ refSet K 3 [0, 1, 3]) (hF2 : F.E 2 = Exch.dirZ K f (z.E 1)) : Opp E F := by
  intro j hj
  have hF1 : F.E 1 = Vsub 3 1 := hF 1 (by decide)
  have hF0 : F.E 0 = ⊥ := by
    have h := hF 0 (by decide)
    simpa [Vsub_zero] using h
  interval_cases j
  · rw [FlagK.E_zero, bot_inf_eq]
  · rw [hF2]
    exact q2cFA2_inf_dirZ_eq_bot hK hfar hbu
  · rw [hF1]
    exact q2cFA2_farSet_inf_Vsub_two hfar
  · rw [hF0, inf_bot_eq]

private theorem q2cFA2_mem_setA2A1_of_mem_intrSet (hK : Nat.card K = (2 ^ f) ^ 2)
    {E : FlagK K 3} {z : FlagK K 2}
    (hy : (E, z) ∈ IntrSet ((flagSys K 2).prod (flagSys K 1))
      {c | c.1 ∈ refSet K 3 [0, 1, 3]} (psiA2A1 hK) 4) :
    (E, z) ∈ setA2A1 K f := by
  simp only [IntrSet, Set.mem_setOf_eq] at hy
  obtain ⟨g, hgR, hgate, hdist⟩ := hy
  have hg1 : g.1 ∈ refSet K 3 [0, 1, 3] := hgR
  obtain ⟨hE3, hz1⟩ := q2cFA2_cdist_prod_eq_four hdist
  have hOpp : Opp E (psiA2A1 hK g).1 := q2cFA2_opp_of_cdist_flagSys_two_eq_three hE3
  have hfar : E ∈ farSet 3 [0, 1, 3] :=
    mem_farSet_of_opp q2cFA2_isCut_013 (q2cFA2_psi_mem hK hg1) hOpp
  have hgate' : IsGateAt ((flagSys K 2).prod (flagSys K 1))
      (refSet K 3 [0, 1, 3] ×ˢ Set.univ) (E, z) g := by
    have h := hgate
    rw [q2cFA2_R₀_eq] at h
    exact h
  obtain ⟨hgate_2, hgate_1⟩ :=
    (q2cFA2_isGateAt_prod (flagSys_connected K 2) (flagSys_connected K 1)).mp hgate'
  have hg1eq : g.1 = gateFlag q2cFA2_isCut_013 hfar :=
    IsGateAt.unique (flagSys_connected K 2) hgate_2
      (q2cFA2_isGateAt_gateFlag (x₀ := stdFlag K 3) q2cFA2_isCut_013 hfar
        (stdFlag_mem_refSet q2cFA2_isCut_013))
  have hg2eq : g.2 = z := by
    have h := hgate_1.2 z (Set.mem_univ z)
    rw [cdist_self (flagSys K 1) z] at h
    have hz0 : cdist (flagSys K 1) z g.2 = 0 := by omega
    exact ((cdist_eq_zero_iff (flagSys K 1) (flagSys_connected K 1)).mp hz0).symm
  have hpsi2 : (psiA2A1 hK g).1.E 2 = Exch.dirZ K f (z.E 1) := by
    rw [q2cFA2_psi_fst_E_two hK hg1, hg2eq]
  have hinf : E.E 1 ⊓ Exch.dirZ K f (z.E 1) = ⊥ := by
    have h := hOpp 1 (by norm_num)
    rw [hpsi2] at h
    exact h
  have hbu : E.E 1 ⊔ Vsub 3 1 ≠ Exch.dirZ K f (z.E 1) := by
    intro heq
    have hle : E.E 1 ≤ Exch.dirZ K f (z.E 1) := by rw [← heq]; exact le_sup_left
    have hEq : E.E 1 ⊓ Exch.dirZ K f (z.E 1) = E.E 1 := inf_eq_left.mpr hle
    have hbot : E.E 1 = ⊥ := by rw [← hEq, hinf]
    have hne : E.E 1 ≠ ⊥ := by
      intro h0
      have hd1 := E.dim 1 (by norm_num)
      rw [h0, finrank_bot] at hd1
      omega
    exact hne hbot
  change E ∈ farSet 3 [0, 1, 3] ∧ blockU K 3 [0, 1, 3] E.E 1 1 ≠
    Vsub 3 1 ⊔ Submodule.span K ((fun v : Fin 2 → K =>
      (![0, sg K f (v 0), sg K f (v 1)] : Fin 3 → K)) '' (z.E 1 : Set (Fin 2 → K)))
  refine ⟨hfar, ?_⟩
  rw [q2cFA2_blockU_013]
  change E.E 1 ⊔ Vsub 3 1 ≠ Vsub 3 1 ⊔
    Submodule.span K (jShift21 K f '' (z.E 1 : Set (Fin 2 → K)))
  exact hbu

private theorem q2cFA2_mem_intrSet_of_mem_setA2A1 (hK : Nat.card K = (2 ^ f) ^ 2)
    {E : FlagK K 3} {z : FlagK K 2} (hy : (E, z) ∈ setA2A1 K f) :
    (E, z) ∈ IntrSet ((flagSys K 2).prod (flagSys K 1))
      {c | c.1 ∈ refSet K 3 [0, 1, 3]} (psiA2A1 hK) 4 := by
  have hy' : E ∈ farSet 3 [0, 1, 3] ∧ blockU K 3 [0, 1, 3] E.E 1 1 ≠
      Vsub 3 1 ⊔ Submodule.span K ((fun v : Fin 2 → K =>
        (![0, sg K f (v 0), sg K f (v 1)] : Fin 3 → K)) '' (z.E 1 : Set (Fin 2 → K))) := hy
  obtain ⟨hfar, hbu0⟩ := hy'
  have hbu : E.E 1 ⊔ Vsub 3 1 ≠ Exch.dirZ K f (z.E 1) := by
    rw [q2cFA2_blockU_013] at hbu0
    change E.E 1 ⊔ Vsub 3 1 ≠ Vsub 3 1 ⊔
      Submodule.span K (jShift21 K f '' (z.E 1 : Set (Fin 2 → K)))
    exact hbu0
  let g : FlagK K 3 × FlagK K 2 := (gateFlag q2cFA2_isCut_013 hfar, z)
  have hgR : g.1 ∈ refSet K 3 [0, 1, 3] := gateFlag_mem_refSet q2cFA2_isCut_013 hfar
  have hgate1 : IsGateAt (flagSys K 2) (refSet K 3 [0, 1, 3]) E
      (gateFlag q2cFA2_isCut_013 hfar) :=
    q2cFA2_isGateAt_gateFlag (x₀ := stdFlag K 3) q2cFA2_isCut_013 hfar
      (stdFlag_mem_refSet q2cFA2_isCut_013)
  have hgate2 : IsGateAt (flagSys K 1) Set.univ z z :=
    ⟨Set.mem_univ z, fun q _ => by rw [cdist_self (flagSys K 1) z, zero_add]⟩
  have hgate : IsGateAt ((flagSys K 2).prod (flagSys K 1))
      {c : FlagK K 3 × FlagK K 2 | c.1 ∈ refSet K 3 [0, 1, 3]} (E, z) g := by
    rw [q2cFA2_R₀_eq]
    exact (q2cFA2_isGateAt_prod (flagSys_connected K 2) (flagSys_connected K 1)).mpr
      ⟨hgate1, hgate2⟩
  refine ⟨g, hgR, hgate, ?_⟩
  have hE2 : g.1.E 2 = E.E 1 ⊔ Vsub 3 1 := by
    change (gateFlag q2cFA2_isCut_013 hfar).E 2 = E.E 1 ⊔ Vsub 3 1
    have h := gateFlag_E q2cFA2_isCut_013 hfar (b := 1) (r := 1) (by decide) (by decide)
    simpa [q2cFA2_blockU_013] using h
  have hpsi1 : (psiA2A1 hK g).1.E 2 = Exch.dirZ K f (z.E 1) := by
    have h := q2cFA2_psi_fst_E_two hK hgR
    simpa only [g] using h
  have hOpp : Opp E (psiA2A1 hK g).1 :=
    q2cFA2_opp_psi hK hfar hbu (q2cFA2_psi_mem hK hgR) hpsi1
  have hE3 : cdist (flagSys K 2) E (psiA2A1 hK g).1 = 3 :=
    q2cFA2_cdist_flagSys_two_eq_three_of_opp hOpp
  have hne_z : z ≠ (psiA2A1 hK g).2 := by
    intro heq
    have hE1 : z.E 1 = (psiA2A1 hK g).2.E 1 := by rw [heq]
    rw [q2cFA2_psi_snd_E_one hK hgR, hE2] at hE1
    have hdir : Exch.dirZ K f (z.E 1) = E.E 1 ⊔ Vsub 3 1 := by
      rw [hE1]
      exact q2cFA2_dirZ_span_jShift21Inv_sup hK hfar
    exact hbu hdir.symm
  have hz1 : cdist (flagSys K 1) z (psiA2A1 hK g).2 = 1 :=
    q2cFA2_cdist_flagSys_one_eq_one hne_z
  rw [cdist_prod (flagSys_connected K 2) (flagSys_connected K 1), hE3, hz1]

theorem intrSet_exchA2A1 (hK : Nat.card K = (2 ^ f) ^ 2) :
    IntrSet ((flagSys K 2).prod (flagSys K 1)) {c | c.1 ∈ refSet K 3 [0, 1, 3]}
      (psiA2A1 hK) 4 = setA2A1 K f := by
  ext y
  obtain ⟨E, z⟩ := y
  exact ⟨q2cFA2_mem_setA2A1_of_mem_intrSet hK, q2cFA2_mem_intrSet_of_mem_setA2A1 hK⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

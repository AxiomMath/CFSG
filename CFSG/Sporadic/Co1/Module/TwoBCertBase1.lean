
module


public import CFSG.Sporadic.Co1.Module.TwoBData
public import CFSG.Sporadic.Co1.Module.TwoBSylow

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.OddCentNative Matrix

theorem exists_sBc :
    ∃ s : NativeSporadic.Co1, matHom s = rowsMatrix 24 rowsSB := by
  obtain ⟨kN, hkN⟩ := exists_gen_family nWord1 nWord2
  have hkN' : ∀ l < nGens.size, matHom (kN l) = rowsMatrix 24 nGens[l]! := hkN
  obtain ⟨hNs, -⟩ := repOK_facts repOK_B
  obtain ⟨s, hs⟩ := exists_rep nGens kN hkN' wordB (by rw [hNs]; decide) 6
  exact ⟨s, hs⟩

noncomputable def sBc :
    NativeSporadic.Co1 := Classical.choose exists_sBc

noncomputable def regsGB :
    List NativeSporadic.Co1 := Odd.runEval [Odd.eA, Odd.eB, sBc] progB


theorem matHom_eA : matHom Odd.eA = matA := Odd.mat_eA

theorem matHom_eB : matHom Odd.eB = matB := Odd.mat_eB

theorem initRowsB_size : initRowsB.size = 3 := by simp [initRowsB]

theorem initRowsB_two : initRowsB[2]?.getD (idRows 24) = rowsSB := by simp [initRowsB]

theorem omega_ne_zero : toVecD 24 code4 ≠ 0 := by
  intro h
  have h0 := toVecD_injective (x := code4) (y := 0) (by norm_num [code4]) (by norm_num)
    (h.trans (toVecD_zero 24).symm)
  norm_num [code4] at h0

theorem code4_lt : code4 < 2 ^ 24 := by norm_num [code4]

theorem yRows_get {l : ℕ} (hl : l < yRows.size) : yRows[l]! = rrB (yIdx[l]!) :=
  Odd.map_toArray_get3 rrB yIdx (by simpa [yRows] using hl)

theorem sRows_get {l : ℕ} (hl : l < sRows.size) : sRows[l]! = rrB (sIdx[l]!) :=
  Odd.map_toArray_get3 rrB sIdx (by simpa [sRows] using hl)

theorem sIdx_mem {l : ℕ} (hl : l < sRows.size) : sIdx[l]! ∈ sIdx := by
  have hl' : l < sIdx.length := by simpa [sRows] using hl
  rw [getElem!_pos sIdx l hl']
  exact List.getElem_mem hl'

theorem sRows_size : sRows.size = 6 := by simp [sRows, sIdx]

theorem conj_mem_centralizer {s u : NativeSporadic.Co1}
    (hu : u ∈ Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) (x : NativeSporadic.Co1) :
    x * u * x⁻¹ ∈ Subgroup.centralizer ({x * s * x⁻¹} : Set NativeSporadic.Co1) := by
  have h := map_conj_le_centralizer (S := Subgroup.zpowers u) (s := s)
    (by rwa [Subgroup.zpowers_le]) x
  exact h ⟨u, Subgroup.mem_zpowers u, by simp [MulAut.conj_apply]⟩

theorem getD_two' :
    [Odd.eA, Odd.eB, sBc].getD 2 (1 : NativeSporadic.Co1) = sBc := rfl

noncomputable def W77 : TwoBW := Classical.choose twoB_ok

noncomputable abbrev KB :
    Subgroup NativeSporadic.Co1 :=
  MulAction.stabilizer NativeSporadic.Co1 (toVecD 24 code4) ⊓
    Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)

theorem mem_KB
    {x : NativeSporadic.Co1}
    (hc : x ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1))
    (hf : co1Act x (toVecD 24 code4) = toVecD 24 code4) : x ∈ KB :=
  Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 hf, hc⟩

theorem matHom_sBc :
    matHom sBc = rowsMatrix 24 rowsSB := Classical.choose_spec exists_sBc

attribute [local irreducible] rowsSB

theorem regs_relB :
    Odd.RegsRel matHom regsGB regsRowsB := by
  refine Odd.runRows_spec matHom progB ?_
  refine ⟨by rw [initRowsB_size]; rfl, fun i => ?_⟩
  match i with
  | 0 => exact matHom_eA
  | 1 => exact matHom_eB
  | 2 =>
    rw [initRowsB_two, getD_two']
    exact matHom_sBc
  | i + 3 => simp [rowsMatrix_idRows, initRowsB]

noncomputable def regB
    (i : ℕ) : NativeSporadic.Co1 := regsGB.getD i 1

noncomputable def nB (l : ℕ) :
    NativeSporadic.Co1 := regB (l + 3)

noncomputable def gS
    (l : ℕ) : NativeSporadic.Co1 := regB (sIdx[l]!)

noncomputable def SB :
    Subgroup NativeSporadic.Co1 := Subgroup.closure (gS '' {l | l < sRows.size})

theorem gS_mem {l : ℕ}
    (hl : l < 6) : gS l ∈ SB :=
  Subgroup.subset_closure ⟨l, by rw [Set.mem_ofPred_eq, sRows_size]; exact hl, rfl⟩

section

attribute [local irreducible] regsGB regsRowsB

theorem matHom_regB
    (i : ℕ) : matHom (regB i) = rowsMatrix 24 (rrB i) := by
  have h : ∀ j : ℕ, matHom (regsGB.getD j 1) =
      rowsMatrix 24 (regsRowsB[j]?.getD (idRows 24)) :=
    And.right regs_relB
  simpa only [regB, rrB] using h i

end

attribute [local irreducible] rrB regsRowsB

theorem centB_facts :
    (∀ i ∈ yIdx ++ sIdx ++ eIdx, mulRows 24 (rrB i) rowsSB = mulRows 24 rowsSB (rrB i)) ∧
    (∀ i ∈ sIdx ++ eIdx, isFixedN (transposeRows 24 (rrB i)) code4 = true) ∧
    (∀ i ∈ yIdx ++ sIdx ++ eIdx ++ [43], validRows (rrB i) = true) ∧
    mulRows 24 (rrB gIdx) (rrB 43) = idRows 24 ∧ orderIs (rrB 40) 3 = true ∧
    orderIs (rrB 42) 5 = true := by
  have h := centB_ok
  simp only [centB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem regB_mem_cent
    {i : ℕ} (hi : i ∈ yIdx ++ sIdx ++ eIdx) :
    regB i ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply matHom_injective
  rw [map_mul, map_mul, matHom_regB, matHom_sBc, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
    (centB_facts.1 i hi)]

theorem regB_fix
    {i : ℕ} (hi : i ∈ sIdx ++ eIdx) :
    co1Act (regB i) (toVecD 24 code4) = toVecD 24 code4 := by
  rw [co1Act_eq_mulVec, matHom_regB]
  exact (isFixedN_iff (rrB i) (by norm_num [code4])).1 (centB_facts.2.1 i hi)

theorem fix_sBc_omega :
    co1Act sBc (toVecD 24 code4) = toVecD 24 code4 := by
  obtain ⟨-, -, -, hfixB, -⟩ := repOK_facts repOK_B
  rw [co1Act_eq_mulVec, matHom_sBc]
  exact (isFixedN_iff rowsSB (by norm_num [code4])).1 hfixB

theorem matHom_gi :
    matHom (regB gIdx)⁻¹ = rowsMatrix 24 (rrB 43) := by
  apply matHom_inv_eq
  rw [matHom_regB, ← rowsMatrix_mulRows, centB_facts.2.2.2.1, rowsMatrix_idRows]

theorem ncard_fix_sBc :
    {v : Vec24 | co1Act sBc v = v}.ncard = 2 ^ 12 := by
  obtain ⟨cB1, -⟩ := countsOK_facts counts_B
  have hfix : {v : Vec24 | co1Act sBc v = v} = {v | rowsMatrix 24 rowsSB *ᵥ v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_sBc]
  rw [hfix, cB1]
  norm_num

theorem ncard_fixQ_sBc :
    {v : Vec24 | co1Act sBc v = v ∧ q₀ v = 1}.ncard = 0 := by
  obtain ⟨-, cB2⟩ := countsOK_facts counts_B
  have hfix : {v : Vec24 | co1Act sBc v = v ∧ q₀ v = 1} =
      {v | rowsMatrix 24 rowsSB *ᵥ v = v ∧ q₀ v = 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_sBc]
  rw [hfix, cB2]

section Kernel

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2 Equiv

theorem ok77 : TwoBOK W77 := Classical.choose_spec twoB_ok

theorem rrB_eq {i : ℕ} (hi : i < 44) :
    rrB i = unpackR 24 (getL 0 W77.RB i) := by
  have hi' : i < W77.RB.length := by rw [ok77.rbl]; exact hi
  rw [rrB, ok77.regs, getL_eq, List.getD_eq_getElem _ _ hi']
  simp [hi']

theorem pm_regB
    {i : ℕ} (hi : i < 44) : PM (regB i) (getL 0 W77.RB i) := by
  unfold PM
  rw [matHom_regB, rrB_eq hi]

theorem pm_sBc :
    PM sBc (getL 0 W77.RB 2) := by
  unfold PM
  rw [matHom_sBc, ok77.sb]

set_option maxRecDepth 20000 in
theorem tr77 :
    trK 24 (getL 0 W77.RB 3) = W77.N1T ∧ trK 24 (getL 0 W77.RB 4) = W77.N2T ∧
    trK 24 (getL 0 W77.RB 2) = W77.SBT ∧
    (∀ k < 2, trK 24 (W77.YR.getD k 0) = W77.YT.getD k 0) ∧
    (∀ k < 6, trK 24 (W77.SR.getD k 0) = W77.ST.getD k 0) ∧
    (∀ k < 5, trK 24 (W77.EM.getD k 0) = W77.ET.getD k 0) ∧
    (∀ k < 4, trK 24 (W77.UM.getD k 0) = W77.UT.getD k 0) := by
  obtain ⟨h1, h⟩ := andB_true ok77.tr
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h⟩ := andB_true h
  obtain ⟨h6, h7⟩ := andB_true h
  have hEM : W77.EM.length = 5 := ok77.lens.2.1
  have hUM : W77.UM.length = 4 := by rw [(zip_spec [] ok77.u).1, ok77.lens.2.2.1]
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun k hk => Nat.eq_of_beq_eq_true ((zip_spec 0 h4).2 k hk),
    fun k hk => Nat.eq_of_beq_eq_true ((zip_spec 0 h5).2 k hk),
    fun k hk => Nat.eq_of_beq_eq_true ((zip_spec 0 h6).2 k (by rw [hEM]; exact hk)),
    fun k hk => Nat.eq_of_beq_eq_true ((zip_spec 0 h7).2 k (by rw [hUM]; exact hk))⟩

theorem pm_nB
    {l : ℕ} (hl : l < 2) :
    PM (nB l) (getL 0 [getL 0 W77.RB 3, getL 0 W77.RB 4] l) := by
  rcases l with _ | _ | l
  · change PM (regB 3) (getL 0 W77.RB 3)
    exact pm_regB (by norm_num)
  · change PM (regB 4) (getL 0 W77.RB 4)
    exact pm_regB (by norm_num)
  · omega

noncomputable def F77 : Frame NativeSporadic.Co1 Vec24 (Fin 24) :=
  co1Frame (toVecD 24 code4) (frA W77.AP) (frA_dist ok77.dist ok77.sym code4_lt)

theorem ncard_fix_orbit_le :
    {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)) |
      co1Act sBc w = w}.ncard ≤ 4095 := by
    have h0 : (0 : Vec24) ∉
        Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)) := by
      rintro ⟨g, hg⟩
      refine omega_ne_zero (co1Act_injective g (hg.trans ?_))
      simp [co1Act_eq_mulVec]
    have hsub : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)) |
        co1Act sBc w = w} ⊆ {v : Vec24 | co1Act sBc v = v} \ {0} :=
      fun w hw => ⟨hw.2, fun h => h0 (Set.mem_singleton_iff.1 h ▸ hw.1)⟩
    have h0mem : (0 : Vec24) ∈ {v : Vec24 | co1Act sBc v = v} := by
      simp [co1Act_eq_mulVec]
    calc _ ≤ ({v : Vec24 | co1Act sBc v = v} \ {0}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 4095 := by
        rw [Set.ncard_sdiff_singleton_of_mem h0mem, ncard_fix_sBc]
        norm_num

theorem exists_orbit_family :
    ∃ t : ℕ → NativeSporadic.Co1,
      (∀ i < 4095, t i ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) ∧
      (∀ i < 4095, ∀ j < 4095,
        co1Act (t i) (toVecD 24 code4) = co1Act (t j) (toVecD 24 code4) → i = j) := by
  obtain ⟨-, -, -, htrY, -⟩ := tr77
  let yg : ℕ → NativeSporadic.Co1 := fun l => regB (if l = 0 then 8 else 12)
  have hY : ∀ l < 2, yg l ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1) ∧
      PM (yg l) (W77.YR.getD l 0) := by
    intro l hl
    rcases l with _ | _ | l
    · change regB 8 ∈ _ ∧ PM (regB 8) (getL 0 W77.RB 8)
      exact ⟨regB_mem_cent (by simp [yIdx]), pm_regB (by norm_num)⟩
    · change regB 12 ∈ _ ∧ PM (regB 12) (getL 0 W77.RB 12)
      exact ⟨regB_mem_cent (by simp [yIdx]), pm_regB (by norm_num)⟩
    · omega
  obtain ⟨t, ht, hd⟩ := tree_family_vec _ ok77.ty code4_lt yg (fun l hl => (hY l hl).1)
    (fun l hl v => by rw [pm_act (MT := W77.YT.getD l 0) (hY l hl).2 (htrY l hl), getL_eq])
  rw [ok77.tyl] at ht hd
  exact ⟨t, ht, hd⟩

theorem gw77 :
    toVecD 24 W77.GW = co1Act (regB gIdx) (toVecD 24 code4) := by
  obtain ⟨-, -, -, htrY, -⟩ := tr77
  obtain ⟨h1, -⟩ := andB_true ok77.gw
  change toVecD 24 W77.GW = co1Act (regB 8) (toVecD 24 code4)
  rw [pm_act (MT := W77.YT.getD 0 0) (pm_regB (i := 8) (by norm_num)) (htrY 0 (by norm_num)),
    ← getL_eq, Nat.eq_of_beq_eq_true h1]

end Kernel

theorem fix_eq_orbit
    {v : Vec24} (hv : co1Act sBc v = v) (hv0 : v ≠ 0) :
    ∃ t ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1),
      co1Act t (toVecD 24 code4) = v := by
  obtain ⟨t, ht, hdist⟩ := exists_orbit_family
  let Img : Set Vec24 := (fun i => co1Act (t i) (toVecD 24 code4)) '' Set.Iio 4095
  have hinj : Set.InjOn (fun i => co1Act (t i) (toVecD 24 code4)) (Set.Iio 4095) :=
    fun i hi j hj e => hdist i hi j hj e
  have hImgcard : Img.ncard = 4095 := by
    rw [Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]
  have hsub : Img ⊆ {w : Vec24 | co1Act sBc w = w} \ {0} := by
    rintro _ ⟨i, hi, rfl⟩
    have hmem := Subgroup.mem_centralizer_singleton_iff.1 (ht i hi)
    refine ⟨?_, fun h => omega_ne_zero (co1Act_injective (t i) (h.trans ?_))⟩
    · show co1Act sBc (co1Act (t i) (toVecD 24 code4)) = co1Act (t i) (toVecD 24 code4)
      rw [← co1Act_mul, ← hmem, co1Act_mul, fix_sBc_omega]
    · simp [co1Act_eq_mulVec]
  have h0mem : (0 : Vec24) ∈ {w : Vec24 | co1Act sBc w = w} := by simp [co1Act_eq_mulVec]
  have hcard : ({w : Vec24 | co1Act sBc w = w} \ {0}).ncard ≤ Img.ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem h0mem, ncard_fix_sBc, hImgcard]
    norm_num
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hvmem : v ∈ {w : Vec24 | co1Act sBc w = w} \ {0} := ⟨hv, hv0⟩
  rw [← heq] at hvmem
  obtain ⟨i, hi, hie⟩ := hvmem
  exact ⟨t i, ht i hi, hie⟩

section

attribute [local irreducible] regB regsGB

theorem matHom_gS :
    ∀ l < sRows.size, matHom (gS l) = rowsMatrix 24 sRows[l]! := by
  intro l hl
  rw [sRows_get hl]
  simpa only [gS] using (matHom_regB (sIdx[l]!))

end

theorem SB_le_cent :

    SB ≤ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1) := by
  rw [SB, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact regB_mem_cent (List.mem_append_left _ (List.mem_append_right _ (sIdx_mem hl)))

theorem SB_fix
    {x : NativeSporadic.Co1} (hx : x ∈ SB) :
    co1Act x (toVecD 24 code4) = toVecD 24 code4 := by
  have hle : SB ≤ stabOf (toVecD 24 code4) := by
    rw [SB, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact regB_fix (List.mem_append_left _ (sIdx_mem hl))
  exact hle hx

section KernelS

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2

attribute [local instance] Odd.vecAct Odd.vecSMul

theorem pm_gS
    {l : ℕ} (hl : l < 6) : PM (gS l) (getL 0 W77.SR l) := by
  have e : gS l = regB (l + 33) := by
    unfold gS
    congr 1
    interval_cases l <;> rfl
  have e2 : getL 0 W77.SR l = getL 0 W77.RB (l + 33) := by
    interval_cases l <;> rfl
  rw [e, e2]
  exact pm_regB (by omega)

theorem exists_S_family :
    ∃ t : ℕ → NativeSporadic.Co1, (∀ i < 2048, t i ∈ SB) ∧ ∀ i < 2048, ∀ j < 2048,
      co1Act (t i) (toVecD 24 W77.GW) = co1Act (t j) (toVecD 24 W77.GW) → i = j := by
  obtain ⟨-, -, -, -, htrS, -⟩ := tr77
  obtain ⟨h1, -⟩ := andB_true ok77.gw
  have hlt : W77.GW < 2 ^ 24 := by
    rw [← Nat.eq_of_beq_eq_true h1]
    exact CFSG.KC.F2W.vmF_lt _ _ _
  obtain ⟨t, ht, hd⟩ := tree_family_vec SB ok77.ts hlt gS (fun l hl => gS_mem hl)
    (fun l hl v => by
      rw [pm_act (MT := W77.ST.getD l 0) (pm_gS hl) (by rw [getL_eq]; exact htrS l hl), getL_eq])
  rw [ok77.tsl] at ht hd
  exact ⟨t, ht, hd⟩

theorem exists_U_family :
    ∃ u : ℕ → NativeSporadic.Co1,
      (∀ i < 16, u i ∈ SB ∧ co1Act (u i) (toVecD 24 W77.GW) = toVecD 24 W77.GW) ∧
      ∀ i < 16, ∀ j < 16, u i = u j → i = j := by
  obtain ⟨-, -, -, -, -, -, htrU⟩ := tr77
  obtain ⟨-, h2⟩ := andB_true ok77.gw
  obtain ⟨-, -, hSWl, -, -⟩ := ok77.lens
  obtain ⟨-, -, -, -, hwS⟩ := ok77.wd
  let uw : ℕ → NativeSporadic.Co1 := fun l => ((W77.SW.getD l []).map gS).prod
  have hpm : ∀ l < 4, PM (uw l) (getL 0 W77.UM l) := by
    intro l hl
    have e := Nat.eq_of_beq_eq_true ((zip_spec [] ok77.u).2 l (by rw [hSWl]; exact hl))
    rw [getL_eq, ← e]
    exact pm_wK _ gS 6 (fun l hl => pm_gS hl) _ (hwS l hl)
  have hmem : ∀ l < 4, uw l ∈ SB := fun l hl =>
    SB.list_prod_mem fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      exact gS_mem (hwS l hl a ha)
  have hfix : ∀ l < 4, co1Act (uw l) (toVecD 24 W77.GW) = toVecD 24 W77.GW := fun l hl => by
    rw [pm_act (MT := W77.UT.getD l 0) (hpm l hl) (by rw [getL_eq]; exact htrU l hl), ← getL_eq,
      Nat.eq_of_beq_eq_true (allN_true h2 l hl)]
  obtain ⟨u, hu, hdu⟩ := tree_family_mat (SB ⊓ stabOf (toVecD 24 W77.GW)) ok77.tu uw
    (fun l hl => Subgroup.mem_inf.2 ⟨hmem l hl, mem_stabOf.2 (hfix l hl)⟩) hpm
  rw [ok77.tul] at hu hdu
  exact ⟨u, fun i hi => ⟨(Subgroup.mem_inf.1 (hu i hi)).1,
    mem_stabOf.1 (Subgroup.mem_inf.1 (hu i hi)).2⟩, hdu⟩

theorem SB_two_pow :
    ∃ m, Nat.card ↥SB = 2 ^ m := by
  have := finite_co1
  obtain ⟨hq1, hq2⟩ := andB_true ok77.q
  refine card_closure_two_pow matHom matHom_injective (rowsMatrix 24 (unpackR 24 W77.Q))
    (rowsMatrix 24 (unpackR 24 W77.QI)) ?_ ?_ _ ?_
  · rw [rM_mul, Nat.eq_of_beq_eq_true hq2, unpackR_idF, rowsMatrix_idRows]
  · rw [rM_mul, Nat.eq_of_beq_eq_true hq1, unpackR_idF, rowsMatrix_idRows]
  · rintro _ ⟨l, hl, rfl⟩
    have hl' : l < 6 := by
      rw [Set.mem_ofPred_eq, sRows_size] at hl
      exact hl
    rw [pm_gS hl', rM_mul, rM_mul]
    exact uniTri_of_check (allN_true ok77.uni l hl')

theorem SB_ge :
    2 ^ 15 ≤ Nat.card ↥SB := by
  have := finite_co1
  obtain ⟨t, ht, hd⟩ := exists_S_family
  obtain ⟨u, hu, hdu⟩ := exists_U_family
  have h := card_mul_le_of_orbit_stab (G := NativeSporadic.Co1) (Ω := Vec24) SB
    (toVecD 24 W77.GW) t u ht hd hu hdu
  calc 2 ^ 15 = 2048 * 16 := by norm_num
    _ ≤ _ := h

theorem SB_dvd :
    2 ^ 15 ∣ Nat.card ↥SB := by
  obtain ⟨m, hm⟩ := SB_two_pow
  exact two_pow_dvd_of_le hm SB_ge

end KernelS

section Order

attribute [local instance] Odd.vecAct Odd.vecSMul

theorem SB_le_KB :
    SB ≤ KB := fun _ hx => mem_KB (SB_le_cent hx) (SB_fix hx)

theorem e3_mem_KB :
    regB 40 ∈ KB :=
  mem_KB (regB_mem_cent (by simp [eIdx])) (regB_fix (by simp [eIdx]))

theorem e5_mem_KB :
    regB 42 ∈ KB :=
  mem_KB (regB_mem_cent (by simp [eIdx])) (regB_fix (by simp [eIdx]))

theorem orderOf_e3 :
    orderOf (regB 40) = 3 :=
  orderOf_eq_of_orderIs (matHom_regB 40) (by norm_num) centB_facts.2.2.2.2.1

theorem orderOf_e5 :
    orderOf (regB 42) = 5 :=
  orderOf_eq_of_orderIs (matHom_regB 42) (by norm_num) centB_facts.2.2.2.2.2

theorem card_KB_ge :
    491520 ≤ Nat.card ↥KB := by
  have h2 : 2 ^ 15 ∣ Nat.card ↥KB := SB_dvd.trans (Subgroup.card_dvd_of_le SB_le_KB)
  have h3 : 3 ∣ Nat.card ↥KB := orderOf_e3 ▸ KB.orderOf_dvd_natCard e3_mem_KB
  have h5 : 5 ∣ Nat.card ↥KB := orderOf_e5 ▸ KB.orderOf_dvd_natCard e5_mem_KB
  have h15 : 3 * 5 ∣ Nat.card ↥KB := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  have h : 2 ^ 15 * (3 * 5) ∣ Nat.card ↥KB :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h15
  exact Nat.le_of_dvd Nat.card_pos h

theorem card_cent_ge :
    2012774400 ≤ Nat.card ↥(Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) := by
  have := finite_co1
  obtain ⟨t, ht, hdist⟩ := exists_orbit_family
  have h1 := Odd.card_mul_card_stab_le (G := NativeSporadic.Co1) (Ω := Vec24)
    (Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) (toVecD 24 code4) 4095 t ht
    (fun i hi j hj e => hdist i hi j hj e)
  have h2 := card_KB_ge
  calc 2012774400 = 4095 * 491520 := by norm_num
    _ ≤ 4095 * Nat.card ↥KB := Nat.mul_le_mul_left _ h2
    _ ≤ _ := h1

end Order

section KernelInter

attribute [local instance] Odd.vecAct Odd.vecSMul

end KernelInter

end CFSG.Sporadic.Co1.Module.TwoB

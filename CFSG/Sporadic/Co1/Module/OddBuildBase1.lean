
module


public import CFSG.Sporadic.Co1.Module.OddChecks

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix CFSG.KC.Odd73 CFSG.KC.Co1F2 CFSG.KD.Co1Odd

attribute [local instance] vecAct vecSMul

attribute [local irreducible] rr regsRows

theorem validOK_facts :
    (∀ i < 94, validRows (rr i) = true) ∧ validRows (idRows 24) = true ∧
    mulRows 24 (rr 23) (rr 24) = idRows 24 ∧ mulRows 24 (rr 17) (rr 25) = idRows 24 ∧
    (∀ i < 8, mulRows 24 (rr (brayIdx[i]!)) (rr (brayInvIdx[i]!)) = idRows 24) ∧
    isT4 code4 = true := by
  have h := validOK_true
  simp only [validOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩ := h
  exact ⟨hA, hB, hC, hD, hE, hF⟩

theorem fixOK_facts :
    (∀ i ∈ [23, 17, 27, 86] ++ brayIdx ++ sIdx ++ zIdx.flatten, isFixedN (Mt i) code4 = true) ∧
    mulRows 24 (rr 27) (rr 27) = idRows 24 ∧ mulRows 24 (rr 86) (rr 86) = idRows 24 ∧
    (∀ i ∈ brayIdx, mulRows 24 (rr i) (rr 27) = mulRows 24 (rr 27) (rr i)) := by
  have h := fixOK_true
  simp only [fixOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := h
  exact ⟨hA, hB, hC, hD⟩

theorem partnerOK_facts :
    ∀ k < 3, (∀ z ∈ zIdx[k]!, mulRows 24 (rr z) (rr 27) = mulRows 24 (rr 27) (rr z) ∧
      mulRows 24 (rr z) (rr (sIdx[k]!)) = mulRows 24 (rr (sIdx[k]!)) (rr z)) ∧
      mulRows 24 (rr (pvIdx[k]!)) (rr (pvIdx[k]! + 1)) = idRows 24 ∧
      rr (sIdx[k]!) = mulRows 24 (mulRows 24 (rr (pvIdx[k]!)) (rr 27)) (rr (pvIdx[k]! + 1)) := by
  have h := partnerOK_true
  simp only [partnerOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  intro k hk
  obtain ⟨⟨hA, hB⟩, hC⟩ := h k hk
  exact ⟨fun z hz => hA z hz, hB, hC⟩

theorem conjOK_facts :
    mulRows 24 (rr 91) (rr 27) = mulRows 24 (rr 89) (rr 91) ∧
    mulRows 24 (rr 93) (rr 89) = mulRows 24 (rr 86) (rr 93) ∧
    orderN (mulRows 24 (rr 27) (rr 70)) = 3 ∧ orderN (mulRows 24 (rr 27) (rr 73)) = 3 ∧
    orderN (mulRows 24 (rr 27) (rr 76)) = 5 := by
  have h := conjOK_true
  simp only [conjOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
  exact ⟨hA, hB, hC, hD, hE⟩

theorem reg_fix_of_mem
    {i : ℕ} (hi : i ∈ [23, 17, 27, 86] ++ brayIdx ++ sIdx ++ zIdx.flatten) :
    reg i ∈ Hst :=
  MulAction.mem_stabilizer_iff.2 (reg_fix (fixOK_facts.1 i hi))

theorem rho3_mem :
    rho3 ∈ Hst := reg_fix_of_mem (by decide)

theorem t1_mem :
    t1 ∈ Hst := reg_fix_of_mem (by decide)

theorem n1_mem :
    n1 ∈ Hst := reg_fix_of_mem (by decide)

theorem n2_mem :
    n2 ∈ Hst := reg_fix_of_mem (by decide)

theorem sRep_mem
    (k : Fin 3) : sRep k ∈ Hst := by
  apply reg_fix_of_mem
  fin_cases k <;> decide

theorem rho3_sq :
    rho3 * rho3 = 1 := reg_mul_eq_one fixOK_facts.2.1

theorem t1_sq :
    t1 * t1 = 1 := reg_mul_eq_one fixOK_facts.2.2.1

theorem rho3_inv :
    rho3⁻¹ = rho3 := inv_eq_of_mul_eq_one_right rho3_sq

theorem t1_inv :
    t1⁻¹ = t1 := inv_eq_of_mul_eq_one_right t1_sq

theorem t1_conj :
    IsConj rho3 t1 := by
  obtain ⟨hA, hB, -⟩ := conjOK_facts
  have h1 : reg 91 * reg 27 = reg 89 * reg 91 := by
    apply mat_injective
    simp only [map_mul, mat_reg]
    rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows, hA]
  have h2 : reg 93 * reg 89 = reg 86 * reg 93 := by
    apply mat_injective
    simp only [map_mul, mat_reg]
    rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows, hB]
  refine isConj_iff.2 ⟨reg 93 * reg 91, ?_⟩
  have : reg 93 * reg 91 * reg 27 = reg 86 * (reg 93 * reg 91) := by
    calc reg 93 * reg 91 * reg 27 = reg 93 * (reg 91 * reg 27) := by rw [mul_assoc]
      _ = reg 93 * (reg 89 * reg 91) := by rw [h1]
      _ = (reg 93 * reg 89) * reg 91 := by rw [mul_assoc]
      _ = (reg 86 * reg 93) * reg 91 := by rw [h2]
      _ = reg 86 * (reg 93 * reg 91) := by rw [mul_assoc]
  exact (mul_inv_eq_iff_eq_mul.2 this)

theorem sRep_conj
    (k : Fin 3) : IsConj rho3 (sRep k) := by
  have h := partnerOK_facts k.1 k.2
  obtain ⟨-, hinv, hdef⟩ := h
  have hs : reg (sIdx[(k : ℕ)]!) = reg (pvIdx[(k : ℕ)]!) * reg 27 * reg (pvIdx[(k : ℕ)]! + 1) := by
    apply mat_injective
    rw [mat_reg, map_mul, map_mul, mat_reg, mat_reg, mat_reg, ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows, ← hdef]
  have hi : reg (pvIdx[(k : ℕ)]! + 1) = (reg (pvIdx[(k : ℕ)]!))⁻¹ := (reg_inv hinv).symm
  unfold sRep
  rw [hs, hi]
  exact isConj_iff.2 ⟨reg (pvIdx[(k : ℕ)]!), rfl⟩

theorem order_rho3_sRep :
    orderOf (rho3 * sRep 0) = 3 ∧ orderOf (rho3 * sRep 1) = 3 ∧
    orderOf (rho3 * sRep 2) = 5 := by
  obtain ⟨-, -, h0, h1, h2⟩ := conjOK_facts
  have hv := validOK_facts.1
  have key : ∀ (i : ℕ), i < 94 → (∀ n, orderN (mulRows 24 (rr 27) (rr i)) = n → 0 < n →
      orderOf (reg 27 * reg i) = n) := by
    intro i hi n hn hpos
    have hval : validRows (mulRows 24 (rr 27) (rr i)) = true :=
      validRows_mulRows (hv 27 (by norm_num)) (hv i hi)
    have := orderOf_eq_of_orderN hval (x := reg 27 * reg i) (by
      rw [map_mul, mat_reg, mat_reg, rowsMatrix_mulRows]) (by rw [hn]; exact hpos)
    rw [this, hn]
  exact ⟨key 70 (by norm_num) 3 h0 (by norm_num), key 73 (by norm_num) 3 h1 (by norm_num),
    key 76 (by norm_num) 5 h2 (by norm_num)⟩

theorem orders_facts
    {r : ℕ} (hr : r < 94) {F : Forest}
    (hF : ∀ i < F.pts.size, validRows F.pts[i]! = true)
    (f : ℕ → NativeSporadic.Co1) (hf : ∀ i < F.pts.size, mat (f i) = rowsMatrix 24 F.pts[i]!)
    (hz : zeroCount (ordersWith (rr r) F) = 0) :
    ∀ i < F.pts.size, 0 < (ordersWith (rr r) F)[i]! ∧
      orderOf (reg r * f i) = (ordersWith (rr r) F)[i]! := by
  intro i hi
  have hz' : (ordersWith (rr r) F)[i]! ≠ 0 := by
    have h0 := hz
    unfold zeroCount at h0
    rw [countBelow_eq, zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    have hsz : i < (ordersWith (rr r) F).size := by simpa [ordersWith] using hi
    have := h0 (Finset.mem_range.2 hsz)
    simpa using this
  have hpos : 0 < (ordersWith (rr r) F)[i]! := Nat.pos_of_ne_zero hz'
  refine ⟨hpos, ?_⟩
  rw [ordersWith_get _ _ hi] at hpos ⊢
  have hval : validRows (mulRows 24 (rr r) F.pts[i]!) = true :=
    validRows_mulRows (validOK_facts.1 r hr) (hF i hi)
  rw [← orderOf_eq_of_orderN hval (x := reg r * f i) (by
    rw [map_mul, mat_reg, hf i hi, rowsMatrix_mulRows]) hpos]

theorem fixOK₂_facts : fixCount [Mt 27] = 65536 ∧
    fixCount4 [Mt 27] (transposeRows 24 qRows) (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 = 32535 := by
  have h := fixOK₂_true
  simp only [fixOK₂, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem Z_forest
    {k n : ℕ} (hk : k < 3) (h : forestZOK k n = true) :
    ∃ z : ℕ → NativeSporadic.Co1,
      (∀ i < n, z i ∈ Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
        Subgroup.centralizer ({reg (sIdx[k]!)} : Set NativeSporadic.Co1)) ∧
      (∀ i < n, ∀ j < n, z i = z j → i = j) ∧
      (∀ i < n, mat (z i) = rowsMatrix 24 (FZ k).pts[i]!) := by
  obtain ⟨hOK, hsz⟩ := forestZOK_facts h
  have hpk := partnerOK_facts k hk
  have hzk : zIdx[k]! ∈ zIdx := by interval_cases k <;> simp [zIdx]
  have hzmem : ∀ l < (zIdx[k]!).length, reg ((zIdx[k]!)[l]!) ∈ Hst ⊓
      Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({reg (sIdx[k]!)} : Set NativeSporadic.Co1) := by
    intro l hl
    have hzin : (zIdx[k]!)[l]! ∈ zIdx[k]! := by
      rw [getElem!_pos (zIdx[k]!) l hl]
      exact List.getElem_mem hl
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨reg_fix_of_mem ?_,
      reg_mem_centralizer (hpk.1 _ hzin).1⟩, ?_⟩
    · simp only [List.mem_append]
      exact Or.inr (List.mem_flatten.2 ⟨zIdx[k]!, hzk, hzin⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact reg_comm (hpk.1 _ hzin).2
  have hQsize : (QZ k).size = (zIdx[k]!).length := by simp [QZ]
  obtain ⟨z, hz, hinj⟩ := forest_mul_sound hOK (fun l hl => PZ_get k l hl) rfl
    (fun l => reg ((zIdx[k]!)[l]!))
    (fun l hl => by
      rw [mat_reg, show (QZ k)[l]! = rr ((zIdx[k]!)[l]!) from
        map_toArray_get (zIdx[k]!) (hQsize ▸ hl)])
    (Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({reg (sIdx[k]!)} : Set NativeSporadic.Co1))
    (fun l hl => hzmem l (hQsize ▸ hl))
  rw [hsz] at hz hinj
  exact ⟨z, fun i hi => (hz i hi).1, hinj, fun i hi => (hz i hi).2⟩

theorem fix_rho3 :
    {ω : Vec24 | rho3 • ω = ω}.ncard = 65536 := by
  have h := ncard_fixedSet [rr 27]
  have e : {ω : Vec24 | rho3 • ω = ω} =
      {v | ∀ M ∈ [rr 27], rowsMatrix 24 M *ᵥ v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, List.mem_singleton, forall_eq]
    exact smul_reg_iff 27 v
  rw [e, h]
  exact fixOK₂_facts.1

theorem oddHyp73 : OddHyp73 Hst where
  ρ_sq := rho3_sq
  ρ_mem := rho3_mem
  t₁_mem := t1_mem
  t₁_conj := t1_conj
  s_mem k hk := by
    have := sRep_mem ⟨k, hk⟩
    rwa [sRep, sIdx_J73 hk] at this
  s_conj k hk := by
    have := sRep_conj ⟨k, hk⟩
    rwa [sRep, sIdx_J73 hk] at this
  s_odd k hk := by
    obtain ⟨h0, h1, h2⟩ := order_rho3_sRep
    interval_cases k
    · exact ⟨1, h0.trans rfl⟩
    · exact ⟨1, h1.trans rfl⟩
    · exact ⟨2, h2.trans rfl⟩
  gen_mem l hl := by
    interval_cases l <;> exact reg_fix_of_mem (by decide)
  gen_inv l hl := by
    have hb := validOK_facts.2.2.2.2.1
    interval_cases l
    · exact (reg_inv (hb 0 (by norm_num))).symm
    · exact (reg_inv (hb 1 (by norm_num))).symm
    · exact (reg_inv (hb 2 (by norm_num))).symm
    · exact (reg_inv (hb 3 (by norm_num))).symm
    · exact (reg_inv (hb 4 (by norm_num))).symm
    · exact (reg_inv (hb 5 (by norm_num))).symm
    · exact (reg_inv (hb 6 (by norm_num))).symm
    · exact (reg_inv (hb 7 (by norm_num))).symm
    · exact (reg_inv validOK_facts.2.2.1).symm
    · exact (reg_inv validOK_facts.2.2.2.1).symm
  bray l hl := by
    have h := fixOK_facts.2.2.2
    interval_cases l <;> exact reg_comm (h _ (by decide))
  z0 i hi := by
    have hp := (partnerOK_facts 0 (by norm_num)).1 i (by simpa [zIdx] using hi)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨reg_fix_of_mem ?_,
      reg_mem_centralizer hp.1⟩, Subgroup.mem_centralizer_singleton_iff.2 (reg_comm hp.2)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  z1 i hi := by
    have hp := (partnerOK_facts 1 (by norm_num)).1 i (by simpa [zIdx] using hi)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨reg_fix_of_mem ?_,
      reg_mem_centralizer hp.1⟩, Subgroup.mem_centralizer_singleton_iff.2 (reg_comm hp.2)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  z2 i hi := by
    have hp := (partnerOK_facts 2 (by norm_num)).1 i (by simpa [zIdx] using hi)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨reg_fix_of_mem ?_,
      reg_mem_centralizer hp.1⟩, Subgroup.mem_centralizer_singleton_iff.2 (reg_comm hp.2)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> decide

theorem z_tree_facts73 {W : OddW}
    (hW : OddOK W) {k : ℕ} (hk : k < 3) :
    ∃ z : ℕ → NativeSporadic.Co1, (∀ i < ![384, 1344, 96] ⟨k, hk⟩, z i ∈ Hst ⊓
      Subgroup.centralizer {rho3} ⊓ Subgroup.centralizer {sRep ⟨k, hk⟩} ∧
        (k ≠ 0 → (∀ v : Vec24, rho3 • v = v → sRep ⟨k, hk⟩ • v = v → z i • v = v) → z i = 1)) ∧
      ∀ i < ![384, 1344, 96] ⟨k, hk⟩, ∀ j < ![384, 1344, 96] ⟨k, hk⟩, z i = z j → i = j := by
  interval_cases k
  · obtain ⟨z, hz, hinj⟩ := zTree0_73 hW oddHyp73
    exact ⟨z, fun i hi => ⟨(hz i hi).1, fun h => absurd rfl h⟩, hinj⟩
  · obtain ⟨z, hz, hinj⟩ := zTree1_73 hW oddHyp73
    refine ⟨z, fun i hi => ⟨(hz i hi).1, fun _ hfix => ?_⟩, hinj⟩
    have hl : i < Z1P.length := by
      have := (treeOK71_facts73 hW.z1).1
      change i < 1344 at hi
      omega
    refine faith73 hW (r := 73) (by norm_num) hW.faith1 hl (hz i hi).2 fun v h1 h2 => ?_
    have := hfix v (by rw [smul_eq_co1Act]; exact h1) (by rw [smul_eq_co1Act]; exact h2)
    rwa [smul_eq_co1Act] at this
  · obtain ⟨z, hz, hinj⟩ := zTree2_73 hW oddHyp73
    refine ⟨z, fun i hi => ⟨(hz i hi).1, fun _ hfix => ?_⟩, hinj⟩
    have hl : i < Z2P.length := by
      have := (treeOK71_facts73 hW.z2).1
      change i < 96 at hi
      omega
    refine faith73 hW (r := 76) (by norm_num) hW.faith2 hl (hz i hi).2 fun v h1 h2 => ?_
    have := hfix v (by rw [smul_eq_co1Act]; exact h1) (by rw [smul_eq_co1Act]; exact h2)
    rwa [smul_eq_co1Act] at this

theorem card_Hcent_ge_lit :
    2752512 ≤ Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) := by
  obtain ⟨W, hW⟩ := lit_ok
  exact card_CH_ge73 hW oddHyp73

end CFSG.Sporadic.Co1.Module.Odd

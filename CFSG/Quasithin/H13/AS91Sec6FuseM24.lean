module

public import CFSG.Quasithin.H13.AS91Sec6Kzero
public import CFSG.Quasithin.H13.AS91Sec6M24
public import CFSG.Quasithin.H13.AS91Sec5ToddDefs
public import Certificates.Certificate89024

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem fuse_exists_word {H : Subgroup S24} {ls : List (Array ℕ)}
    (hl : ∀ t ∈ ls, ∃ σ ∈ H, RepT t σ) (w : List ℕ) :
    ∃ σ ∈ H, RepT (Native.fuseWord ls w) σ := by
  have key : ∀ (w : List ℕ) (t : Array ℕ), (∃ σ ∈ H, RepT t σ) →
      ∃ σ ∈ H, RepT (w.foldl (fun t j => Native.kzeroMul t (ls.getD j Native.kzeroId)) t) σ := by
    intro w
    induction w with
    | nil => exact fun t ht => ht
    | cons j w ih =>
      rintro t ⟨σ, hσ, hrep⟩
      refine ih _ ?_
      obtain ⟨τ, hτ, hτr⟩ : ∃ τ ∈ H, RepT (ls.getD j Native.kzeroId) τ := by
        by_cases h : j < ls.length
        · rw [List.getD_eq_getElem _ _ h]
          exact hl _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (not_lt.1 h)]
          exact ⟨1, H.one_mem, kz_repT_one⟩
      exact ⟨σ * τ, H.mul_mem hσ hτ, kz_repT_mul hrep hτr⟩
  exact key w _ ⟨1, H.one_mem, kz_repT_one⟩

theorem fuse_conj_tree {H : Subgroup S24} {ps : List (Array ℕ × Array ℕ)}
    (hp : ∀ p ∈ ps, ∃ τ ∈ H, RepT p.1 τ ∧ RepT p.2 τ⁻¹) {x : Array ℕ} {x₀ : S24}
    (hx : RepT x x₀) {r : Array (Array ℕ) × Array ℕ × Array ℕ}
    (h : Native.treeValid Native.kzeroValid (Native.fuseConjSteps ps) x r = true) :
    ∀ q ∈ r.1.toList, ∃ σ ∈ H, RepT q (σ * x₀ * σ⁻¹) := by
  obtain ⟨-, h0, hall⟩ := treeValid_get h
  have key : ∀ j, j < r.1.size → ∃ σ ∈ H, RepT r.1[j]! (σ * x₀ * σ⁻¹) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases (hall j hj).2 with rfl | ⟨hpar, hgen, hstp⟩
      · refine ⟨1, H.one_mem, ?_⟩
        rw [h0, inv_one, one_mul, mul_one]
        exact hx
      · obtain ⟨σ, hσ, hσf⟩ := ih r.2.1[j]! hpar (lt_trans hpar hj)
        have hgm : r.2.2[j]! < ps.length := by simpa [Native.fuseConjSteps] using hgen
        obtain ⟨τ, hτ, hτ1, hτ2⟩ := hp (ps.getD r.2.2[j]! (#[], #[]))
          (by rw [List.getD_eq_getElem _ _ hgm]; exact List.getElem_mem hgm)
        refine ⟨τ * σ, H.mul_mem hτ hσ, ?_⟩
        have e : ((Native.fuseConjSteps ps).getD r.2.2[j]! id) r.1[r.2.1[j]!]! =
            Native.kzeroConj (ps.getD r.2.2[j]! (#[], #[])) r.1[r.2.1[j]!]! := by
          unfold Native.fuseConjSteps
          rw [getD_map_of_lt _ ps (#[], #[]) id hgm]
        rw [← hstp, e]
        have h1 := kz_repT_conj hτ1 hτ2 hσf
        have e2 : τ * (σ * x₀ * σ⁻¹) * τ⁻¹ = τ * σ * x₀ * (τ * σ)⁻¹ := by group
        rwa [e2] at h1
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hq)
  obtain ⟨σ, hσ, hσf⟩ := key j hj
  rw [getElem!_pos r.1 j hj] at hσf
  exact ⟨σ, hσ, hσf⟩

theorem fuse_xorClose_mem {H : Subgroup W11} {gs : List ℕ} (hg : ∀ g ∈ gs, toW 11 g ∈ H) :
    ∀ x ∈ Native.fuseXorClose gs, toW 11 x ∈ H := by
  have key : ∀ (gs L : List ℕ), (∀ g ∈ gs, toW 11 g ∈ H) → (∀ x ∈ L, toW 11 x ∈ H) →
      ∀ x ∈ gs.foldl (fun L g => if L.contains g then L else L ++ L.map (· ^^^ g)) L,
        toW 11 x ∈ H := by
    intro gs
    induction gs with
    | nil => exact fun L _ hL => hL
    | cons g gs ih =>
      intro L hg hL
      refine ih _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_
      dsimp only
      split_ifs
      · exact hL
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hL x hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          rw [toW_xor]
          exact H.mul_mem (hL y hy) (hg g List.mem_cons_self)
  exact key gs [0] hg (by simp [toW_zero, H.one_mem])

private theorem fuse_toddPopc_eq (k a : ℕ) : Native.toddPopc k a = popc k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [Native.toddPopc, popc, ih]

private theorem fuse_toddEven_iff (k a : ℕ) :
    Native.toddEven k a = true ↔ ((popc k a : ℕ) : ZMod 2) = 0 := by
  rw [Native.toddEven, fuse_toddPopc_eq, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  simp

private theorem fuse_octFun_maskFin_toW (o m : ℕ) :
    octFun (maskFin o) (toW 11 m) = ((popc 24 (o &&& actM liftECols m) : ℕ) : ZMod 2) := by
  rw [octFun_def, toAdd_toW, liftE_bvec, ← bvec_dotProduct]
  simp only [dotProduct, bvec_apply, maskFin]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : o.testBit i = true <;> simp [h]

private theorem fuse_toddOct_iff (o m : ℕ) :
    Native.toddOct o m = true ↔ octFun (maskFin o) (toW 11 m) = 0 := by
  have e : Native.actM Native.liftEColsN m = actM liftECols m := actM_eq_actM _ _
  rw [fuse_octFun_maskFin_toW, Native.toddOct, fuse_toddEven_iff, e]

private theorem fuse_mem_annOf_toFinset_map (os : List ℕ) (m : ℕ) :
    toW 11 m ∈ annOf ((os.map maskFin).toFinset) ↔ Native.toddOctsKer os m = true := by
  rw [mem_annOf, Native.toddOctsKer, List.all_eq_true]
  constructor
  · intro h o ho
    exact (fuse_toddOct_iff o m).2 (h _ (List.mem_toFinset.2 (List.mem_map.2 ⟨o, ho, rfl⟩)))
  · intro h O hO
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hO)
    exact (fuse_toddOct_iff o m).1 (h o ho)

theorem fuse_mem_annOf_sextFin_zero_iff (m : ℕ) :
    toW 11 m ∈ annOf (octsOf (sextFin 0)) ↔
      Native.toddOctsKer (Native.octsS Native.baseSext) m = true := by
  rw [octsOf_sextFin (by norm_num), sextList_zero]
  exact fuse_mem_annOf_toFinset_map _ _

theorem fuse_toW_toddAct_xor {t : Array ℕ} {k : S24} (hk : k ∈ M24g) (h : RepT t k) (m : ℕ) :
    toW 11 (Native.toddAct t m ^^^ m) =
      rho11 AutPerm le_rfl ⟨k, hk⟩ (toW 11 m) * (toW 11 m)⁻¹ := by
  rw [toW_xor, rho11_toW_native hk h m, inv_eq_of_mul_eq_one_right (W11_mul_self (toW 11 m))]

theorem fuse_one_inv_W11 : (1 : W11)⁻¹ = 1 := inv_eq_of_mul_eq_one_right (W11_mul_self 1)

@[expose] def piA : S24 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]
  left_inv := by decide
  right_inv := by decide

@[expose] def piB : S24 where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20]
  left_inv := by decide
  right_inv := by decide

theorem repT_piA : RepT Native.fusePiATab piA := by
  unfold RepT
  decide +kernel

theorem repT_piB : RepT Native.fusePiBTab piB := by
  unfold RepT
  decide +kernel

theorem piA_sq : piA * piA = 1 := Equiv.ext (by decide +kernel)

theorem piB_sq : piB * piB = 1 := Equiv.ext (by decide +kernel)

theorem piA_apply_eq_iff (i : Fin 24) : piA i = i ↔ i.val < 8 := by
  revert i
  decide +kernel

theorem piB_apply_ne (i : Fin 24) : piB i ≠ i := by
  revert i
  decide +kernel

theorem fuse_repT_pA_inv : RepT Native.pATab bridgePA⁻¹ := by
  unfold RepT
  decide +kernel

theorem fusePairs_mem : ∀ p ∈ Native.fusePairs (), ∃ τ ∈ M24g, RepT p.1 τ ∧ RepT p.2 τ⁻¹ := by
  intro p hp
  simp only [Native.fusePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨bridgePA, bridgePA_mem, repT_pA, fuse_repT_pA_inv⟩
  · exact ⟨bridgePB, bridgePB_mem, repT_pB, repT_pBi⟩
  · exact ⟨bridgePB⁻¹, M24g.inv_mem bridgePB_mem, repT_pBi, by rw [inv_inv]; exact repT_pB⟩

theorem fuseLetters_mem : ∀ t ∈ Native.fuseLetters (), ∃ σ ∈ M24g, RepT t σ := by
  intro t ht
  unfold Native.fuseLetters at ht
  simp only [List.mem_append] at ht
  rcases ht with ((ht | ht) | ht) | ht
  · obtain ⟨j, hj⟩ := exists_repT_of_mem_genTabs ht
    exact ⟨genPerm j, genPerm_mem j, hj⟩
  · obtain ⟨j, hj⟩ := exists_repT_of_mem_lTabs ht
    exact ⟨lPerm j, lPerm_mem j, hj⟩
  · obtain ⟨j, hj⟩ := exists_repT_of_mem_uTabs ht
    exact ⟨uPerm j, uPerm_mem j, hj⟩
  · obtain ⟨j, hj⟩ := exists_repT_of_mem (tabs := Native.s0Tabs) (n := 4) rfl repT_s0Perm ht
    exact ⟨s0Perm j, s0Perm_mem j, hj⟩

section Spec


theorem fuseCheck_true : Native.fuseCheck () = true := Certificates.certificate89024

theorem fuseCheck_parts : Native.fuseCommCheck () = true ∧ Native.fuseDuadCheck () = true ∧
    Native.fusePiCheck () = true ∧ Native.fuseInvCheck () = true ∧ Native.fuseX0Check () = true ∧
    Native.fusePiBCheck () = true ∧ Native.fusePiACheck () = true := by
  have h := fuseCheck_true
  simp only [Native.fuseCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem fuseComm_spec : ∀ m < 2048,
    Native.toddOctsKer (Native.octsS Native.baseSext) m = true →
      m ∈ Native.fuseXorClose (Native.fuseCommGens ()) := by
  have h := fuseCheck_parts.1
  unfold Native.fuseCommCheck Native.fuseCommLoop at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  intro m hm hk
  rcases h m hm with h1 | h1
  · rw [hk] at h1
    exact absurd h1 (by simp)
  · exact h1

theorem fuseDuad_spec :
    Native.toddOctsKer (Native.octsS Native.baseSext) (Native.fuseDuadMask ()) = true :=
  fuseCheck_parts.2.1

theorem fusePi_spec : (Native.kzeroK0List ()).contains Native.fusePiATab = true ∧
    (Native.kzeroK0List ()).contains Native.fusePiBTab = true := by
  have h := fuseCheck_parts.2.2.1
  unfold Native.fusePiCheck at h
  simpa only [Bool.and_eq_true] using h

theorem fuseInv_spec : ∃ rA rB : Array (Array ℕ) × Array ℕ × Array ℕ,
    Native.treeValid Native.kzeroValid (Native.fuseConjSteps (Native.fusePairs ()))
      Native.fusePiATab rA = true ∧
    Native.treeValid Native.kzeroValid (Native.fuseConjSteps (Native.fusePairs ()))
      Native.fusePiBTab rB = true ∧
    ∀ t ∈ (Native.kzeroSyl ()).1.toList, Native.kzeroMul t t = Native.kzeroId →
      t ≠ Native.kzeroId → t ∈ rA.1.toList ∨ t ∈ rB.1.toList := by
  have h := fuseCheck_parts.2.2.2.1
  unfold Native.fuseInvCheck Native.fuseInvLoop at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨hA, hB⟩, hall⟩ := h
  refine ⟨Native.fuseOrbit Native.fusePiATab, Native.fuseOrbit Native.fusePiBTab, hA, hB, ?_⟩
  intro t ht hsq hne
  rcases hall t ht with ((h1 | h1) | h1) | h1
  · exact absurd hsq h1
  · exact absurd h1 hne
  · exact Or.inl h1
  · exact Or.inr h1

theorem fuseX0_spec :
    (∀ t ∈ Native.kzeroK0List (), t ≠ Native.kzeroId →
      Native.kzeroMul (Native.fuseX0Tab ()) t ≠ Native.kzeroMul t (Native.fuseX0Tab ())) ∧
    ∀ m < 2048, Native.toddOctsKer (Native.octsS Native.baseSext)
      (Native.toddAct (Native.fuseX0Tab ()) m ^^^ m) = true := by
  have h := fuseCheck_parts.2.2.2.2.1
  unfold Native.fuseX0Check Native.fuseX0Loop at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun t ht hne => ?_, fun m hm => List.all_eq_true.1 h2 m (List.mem_range.2 hm)⟩
  have h3 := List.all_eq_true.1 h1 t ht
  simp only [Bool.or_eq_true, beq_iff_eq] at h3
  rcases h3 with h3 | h3
  · exact absurd h3 hne
  · exact bne_iff_ne.1 h3

theorem fusePiB_spec : ∀ m < 2048, Native.toddAct Native.fusePiBTab m = m →
    Native.toddOctsKer (Native.octsS Native.baseSext) m = true := by
  have h := fuseCheck_parts.2.2.2.2.2.1
  unfold Native.fusePiBCheck Native.fusePiBLoop at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  intro m hm hfix
  rcases h m hm with h1 | h1
  · exact absurd hfix (bne_iff_ne.1 h1)
  · exact h1

theorem fusePiA_spec :
    (∀ w ∈ Native.fuseSigmaWords,
      Native.kzeroMul (Native.fuseWord (Native.fuseLetters ()) w) Native.fusePiATab =
        Native.kzeroMul Native.fusePiATab (Native.fuseWord (Native.fuseLetters ()) w)) ∧
    ∀ m < 2048, Native.toddAct Native.fusePiATab m = m →
      ∃ w ∈ Native.fuseSigmaWords, Native.toddOctsKer (Native.octsS Native.baseSext)
        (Native.toddAct (Native.fuseWord (Native.fuseLetters ()) w) m) = true := by
  have h := fuseCheck_parts.2.2.2.2.2.2
  unfold Native.fusePiACheck Native.fusePiALoop at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw => beq_iff_eq.1 (List.all_eq_true.1 h1 _ (List.mem_map.2 ⟨w, hw, rfl⟩)),
    fun m hm hfix => ?_⟩
  have h3 := List.all_eq_true.1 h2 m (List.mem_range.2 hm)
  simp only [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · exact absurd hfix (bne_iff_ne.1 h3)
  · obtain ⟨T, hT, hT2⟩ := List.any_eq_true.1 h3
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hT
    exact ⟨w, hw, hT2⟩

end Spec

theorem exists_isDuadClass_mem_annOf :
    ∃ w ∈ annOf (octsOf (sextFin 0)), IsDuadClass w := by
  refine ⟨toW 11 (Native.fuseDuadMask ()), (fuse_mem_annOf_sextFin_zero_iff _).2 fuseDuad_spec, ?_⟩
  have hmem : Native.fuseDuadMask () ∈ Native.duadMasks () := by
    unfold Native.duadMasks
    rw [List.mem_flatMap]
    refine ⟨0, List.mem_range.2 (by norm_num), ?_⟩
    rw [List.mem_map]
    exact ⟨1, List.mem_filter.2 ⟨List.mem_range.2 (by norm_num), by decide⟩, rfl⟩
  obtain ⟨D, hD, hDe⟩ := duadMasks_spec hmem
  exact ⟨D, hD, hDe⟩

section Main


theorem fuse_exists_mem_K0base_of_mem {t : Array ℕ} (ht : t ∈ Native.kzeroK0List ()) :
    ∃ k ∈ K0base, RepT t k := by
  have hd := kzeroData
  have ht' : t ∈ kzK (Native.kzeroSyl ()) := ht
  obtain ⟨σ, -, hσ⟩ := kz_syl_mem hd t (kz_K_sub ht').1
  exact ⟨σ, (mem_K0base_iff_kzK hd).2 ⟨t, ht', hσ⟩, hσ⟩

theorem annOf_le_comm_K0base : ∀ a ∈ annOf (octsOf (sextFin 0)), a ∈
    Subgroup.closure {w | ∃ (k : S24) (hk : k ∈ K0base) (v : W11),
      w = rho11 AutPerm le_rfl ⟨k, K0base_le hk⟩ v * v⁻¹} := by
  intro a ha
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 a
  have hm' : m < 2048 := by simpa using hm
  refine fuse_xorClose_mem (H := Subgroup.closure {w | ∃ (k : S24) (hk : k ∈ K0base) (v : W11),
      w = rho11 AutPerm le_rfl ⟨k, K0base_le hk⟩ v * v⁻¹}) (gs := Native.fuseCommGens ())
      (fun g hg => ?_) m (fuseComm_spec m hm' ((fuse_mem_annOf_sextFin_zero_iff m).1 ha))
  unfold Native.fuseCommGens at hg
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hg
  obtain ⟨t, ht, i, -, rfl⟩ := hg
  obtain ⟨k, hk, hrep⟩ := fuse_exists_mem_K0base_of_mem ht
  exact Subgroup.subset_closure ⟨k, hk, toW 11 (1 <<< i),
    fuse_toW_toddAct_xor (K0base_le hk) hrep (1 <<< i)⟩

theorem piA_mem : piA ∈ K0base := mem_K0base_of_contains repT_piA fusePi_spec.1

theorem piB_mem : piB ∈ K0base := mem_K0base_of_contains repT_piB fusePi_spec.2

theorem fuse_exists_conj_mem_sylS0 {s : S24} (hs : s ∈ M24g) (hs2 : s * s = 1) :
    ∃ τ ∈ M24g, τ * s * τ⁻¹ ∈ sylS0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS0p : IsPGroup 2 sylS0G := IsPGroup.of_card card_sylS0G
  have hidx : sylS0G.index = 239085 := by
    have h := sylS0G.card_mul_index
    rw [card_sylS0G, show Nat.card ↥M24g = 244823040 from CFSG.Monster.Code.card_AutPerm] at h
    norm_num at h
    omega
  have hnd : ¬ 2 ∣ sylS0G.index := by
    rw [hidx]
    norm_num
  let T : Sylow 2 ↥M24g := hS0p.toSylow hnd
  have hT : (T : Subgroup ↥M24g) = sylS0G := IsPGroup.toSylow_coe hS0p hnd
  let x : ↥M24g := ⟨s, hs⟩
  have hxx : x * x = 1 := Subtype.ext hs2
  have hK : ∀ a ∈ Subgroup.zpowers x, a * a = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hxx, one_zpow]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow
    (duad_isPGroup_two_of_sq (K := Subgroup.zpowers x) hK)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M24g T Q
  have hxQ : x ∈ (Q : Subgroup ↥M24g) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply, hT] at hxQ
  refine ⟨((g⁻¹ : ↥M24g) : S24), (g⁻¹).2, ?_⟩
  have h1 := mem_sylS0G.1 hxQ
  have e : ((g⁻¹ * x * g : ↥M24g) : S24) =
      ((g⁻¹ : ↥M24g) : S24) * s * ((g⁻¹ : ↥M24g) : S24)⁻¹ := by simp [x]
  rwa [e] at h1

theorem exists_conj_piA_or_piB {s : S24} (hs : s ∈ M24g) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ σ ∈ M24g, σ * s * σ⁻¹ = piA ∨ σ * s * σ⁻¹ = piB := by
  obtain ⟨τ, hτ, hτS⟩ := fuse_exists_conj_mem_sylS0 hs hs2
  obtain ⟨t, ht, hrep⟩ := kz_syl_enum kzeroData (τ * s * τ⁻¹) hτS
  obtain ⟨rA, rB, hA, hB, hcov⟩ := fuseInv_spec
  have hu2 : τ * s * τ⁻¹ * (τ * s * τ⁻¹) = 1 := by
    calc τ * s * τ⁻¹ * (τ * s * τ⁻¹) = τ * (s * s) * τ⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hu1 : τ * s * τ⁻¹ ≠ 1 := fun h => hs1 (by
    have e : s = τ⁻¹ * (τ * s * τ⁻¹) * τ := by group
    rw [e, h]
    group)
  have htt : Native.kzeroMul t t = Native.kzeroId := by
    have h1 := kz_repT_mul hrep hrep
    rw [hu2] at h1
    exact kz_eq_of_repT h1 kz_repT_one (kz_size_mul _ _) (by decide)
  have htne : t ≠ Native.kzeroId := by
    rintro rfl
    exact hu1 (kz_repT_unique hrep kz_repT_one)
  rcases hcov t ht htt htne with h | h
  · obtain ⟨ν, hν, hνr⟩ := fuse_conj_tree (H := M24g) fusePairs_mem repT_piA hA t h
    have e : τ * s * τ⁻¹ = ν * piA * ν⁻¹ := kz_repT_unique hrep hνr
    refine ⟨ν⁻¹ * τ, M24g.mul_mem (M24g.inv_mem hν) hτ, Or.inl ?_⟩
    calc ν⁻¹ * τ * s * (ν⁻¹ * τ)⁻¹ = ν⁻¹ * (τ * s * τ⁻¹) * ν := by group
      _ = piA := by rw [e]; group
  · obtain ⟨ν, hν, hνr⟩ := fuse_conj_tree (H := M24g) fusePairs_mem repT_piB hB t h
    have e : τ * s * τ⁻¹ = ν * piB * ν⁻¹ := kz_repT_unique hrep hνr
    refine ⟨ν⁻¹ * τ, M24g.mul_mem (M24g.inv_mem hν) hτ, Or.inr ?_⟩
    calc ν⁻¹ * τ * s * (ν⁻¹ * τ)⁻¹ = ν⁻¹ * (τ * s * τ⁻¹) * ν := by group
      _ = piB := by rw [e]; group

theorem exists_x0 : ∃ x₀ ∈ M24g, x₀ • sextFin 0 = sextFin 0 ∧
    (∀ k ∈ K0base, x₀ * k * x₀⁻¹ = k → k = 1) ∧
    ∀ (h : x₀ ∈ M24g) (w : W11), rho11 AutPerm le_rfl ⟨x₀, h⟩ w * w⁻¹ ∈
      annOf (octsOf (sextFin 0)) := by
  have hl : ∀ t ∈ Native.fuseULetters (),
      ∃ σ ∈ M24g ⊓ MulAction.stabilizer S24 (sextFin 0), RepT t σ := by
    intro t ht
    unfold Native.fuseULetters at ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hlen : (Native.kzeroHs ()).length = 8 := by decide +kernel
    have hi8 : i < 8 := hlen ▸ hi
    refine ⟨kzCj ⟨i, hi8⟩, ⟨kzCj_mem _, MulAction.mem_stabilizer_iff.2 (kzCj_fix _)⟩, ?_⟩
    have h1 := (kz_Cj_rep ⟨i, hi8⟩).1
    rwa [Fin.val_mk, List.getD_eq_getElem _ _ hi] at h1
  obtain ⟨σ, hσ, hrep⟩ := fuse_exists_word hl Native.fuseX0Word
  have hrep' : RepT (Native.fuseX0Tab ()) σ := hrep
  obtain ⟨hσM, hσU⟩ := Subgroup.mem_inf.1 hσ
  refine ⟨σ, hσM, MulAction.mem_stabilizer_iff.1 hσU, fun k hk hcomm => ?_, fun h w => ?_⟩
  · obtain ⟨t, ht, hkr⟩ := mem_K0base_iff_native.1 hk
    have hσk : σ * k = k * σ := by
      calc σ * k = σ * k * σ⁻¹ * σ := by group
        _ = k * σ := by rw [hcomm]
    have h1 := kz_repT_mul hrep' hkr
    have h2 := kz_repT_mul hkr hrep'
    rw [hσk] at h1
    have heq := kz_eq_of_repT h1 h2 (kz_size_mul _ _) (kz_size_mul _ _)
    by_contra hk1
    refine (fuseX0_spec.1 t ht ?_) heq
    rintro rfl
    exact hk1 (kz_repT_unique hkr kz_repT_one)
  · obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
    have hm' : m < 2048 := by simpa using hm
    rw [← fuse_toW_toddAct_xor h hrep' m]
    exact (fuse_mem_annOf_sextFin_zero_iff _).2 (fuseX0_spec.2 m hm')

theorem fix_piB_mem_annOf {w : W11}
    (hw : rho11 AutPerm le_rfl ⟨piB, K0base_le piB_mem⟩ w = w) :
    w ∈ annOf (octsOf (sextFin 0)) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hm' : m < 2048 := by simpa using hm
  rw [rho11_toW_native (K0base_le piB_mem) repT_piB m] at hw
  have hfix : Native.toddAct Native.fusePiBTab m = m :=
    toW_inj (by simpa using toddAct_lt repT_piB m) hm hw
  exact (fuse_mem_annOf_sextFin_zero_iff m).2 (fusePiB_spec m hm' hfix)

theorem fix_piB_mem {w : W11}
    (hw : rho11 AutPerm le_rfl ⟨piB, K0base_le piB_mem⟩ w = w) :
    ∃ a ∈ annOf (octsOf (sextFin 0)), ∃ v : W11,
      w = a * (rho11 AutPerm le_rfl ⟨piB, K0base_le piB_mem⟩ v * v⁻¹) := by
  refine ⟨w, fix_piB_mem_annOf hw, 1, ?_⟩
  rw [map_one, fuse_one_inv_W11, mul_one, mul_one]

theorem fix_piA_mem_annOf {w : W11}
    (hw : rho11 AutPerm le_rfl ⟨piA, K0base_le piA_mem⟩ w = w) :
    ∃ (σ : S24) (hσ : σ ∈ M24g), σ * piA = piA * σ ∧
      rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ annOf (octsOf (sextFin 0)) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hm' : m < 2048 := by simpa using hm
  rw [rho11_toW_native (K0base_le piA_mem) repT_piA m] at hw
  have hfix : Native.toddAct Native.fusePiATab m = m :=
    toW_inj (by simpa using toddAct_lt repT_piA m) hm hw
  obtain ⟨c, hc, hcA⟩ := fusePiA_spec.2 m hm' hfix
  obtain ⟨σ, hσ, hrep⟩ := fuse_exists_word (H := M24g) fuseLetters_mem c
  have hcomm : σ * piA = piA * σ := by
    have h1 := kz_repT_mul hrep repT_piA
    have h2 := kz_repT_mul repT_piA hrep
    rw [fusePiA_spec.1 c hc] at h1
    exact kz_repT_unique h1 h2
  refine ⟨σ, hσ, hcomm, ?_⟩
  rw [rho11_toW_native hσ hrep m]
  exact (fuse_mem_annOf_sextFin_zero_iff _).2 hcA

theorem fix_piA_mem {w : W11}
    (hw : rho11 AutPerm le_rfl ⟨piA, K0base_le piA_mem⟩ w = w) :
    ∃ (σ : S24) (hσ : σ ∈ M24g), σ * piA = piA * σ ∧ ∃ a ∈ annOf (octsOf (sextFin 0)),
      ∃ v : W11, rho11 AutPerm le_rfl ⟨σ, hσ⟩ w =
        a * (rho11 AutPerm le_rfl ⟨piA, K0base_le piA_mem⟩ v * v⁻¹) := by
  obtain ⟨σ, hσ, hcomm, hA⟩ := fix_piA_mem_annOf hw
  refine ⟨σ, hσ, hcomm, _, hA, 1, ?_⟩
  rw [map_one, fuse_one_inv_W11, mul_one, mul_one]

end Main

end CFSG.Quasithin.H13.AS91.M24G

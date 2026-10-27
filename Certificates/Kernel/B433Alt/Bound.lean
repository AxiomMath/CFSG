module

public import Certificates.Kernel.B433Alt.CoverY
public import Certificates.Kernel.B433Alt.StFold
public import CFSG.Certificates.Kernel.TwistDce.Cover

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CFSG.YGroups.DCE.B433 CFSG.Certificates.TwDce

@[expose] def liveL : List ℕ := (List.range 64).filter liveB

theorem liveL_len : liveL.length = 46 := by decide

theorem liveL_spec : ∀ j, j ∈ liveL ↔ j < 64 ∧ liveB j = true := by
  intro j
  simp [liveL]

theorem live_iff (j : ℕ) : 0 < CFSG.KD.B4AN.LIVE &&& (1 <<< j) ↔ liveB j = true := by
  unfold liveB CFSG.KD.B4AN.LIVE
  rw [Nat.blt_eq]
  rfl

theorem data_ok : (∀ j < 64, liveB j = true → ∀ i < CFSG.KD.B4AN.RN j, rootE j i < 5965) ∧
    (∀ j < 64, liveB j = true → 0 < CFSG.KD.B4AC.MJ j ∧ 4089470473293004800 % CFSG.KD.B4AC.MJ j = 0) ∧
    (liveL.map fun j => 4089470473293004800 / CFSG.KD.B4AC.MJ j).sum = 2031941058560000 ∧
    (∀ c < 10, c ≠ 7 → fld THM (4 * c) 15 = swapL c) ∧
    liveL.head? = some 0 := by
  decide +kernel

@[expose] noncomputable def swW : ℕ := wMk 90 ((List.range 90).foldr (fun i acc => acc ||| (swSpider.getD i 0 <<< (4 * i))) 0)

theorem swW_ok : wInH swW = true ∧ isOne CFSG.KD.B4A.LP swW = true ∧ wList swW = swSpider := by
  decide +kernel

section

theorem isOne_psi {w : ℕ} (hw : wInH w = true) (h : isOne CFSG.KD.B4A.LP w = true) :
    psi (wVal (yGen 4 3 2) w) = 1 :=
  ker_rho432F_le_ker_psi (isOne_rho hw h)

theorem hsw : psi (evalWord (yGen 4 3 2) swSpider) = 1 := by
  have h := isOne_psi swW_ok.1 swW_ok.2.1
  unfold wVal at h
  rwa [swW_ok.2.2] at h

@[expose] noncomputable def xG (c : ℕ) : Ghat hsw := psiG hsw (yGen 4 3 2 c)

theorem wVal_xG (w : ℕ) : wVal xG w = psiG hsw (wVal (yGen 4 3 2) w) := by
  unfold wVal
  rw [evalWord_map_hom]
  rfl

theorem facts : ∃ X : ℕ → Ghat hsw, X 0 = 1 ∧ ∀ r < 5965,
    (isFact (dKind (CFSG.KD.B4A.RD r)) = true →
      X (dN1 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.PW (dPt (CFSG.KD.B4A.RD r))) * u hsw *
        (X (dN2 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.RW r))⁻¹ ∈ Hh hsw) ∧
    (isStab (dKind (CFSG.KD.B4A.RD r)) = true →
      X (dN2 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.RW r) * (X (dN2 (CFSG.KD.B4A.RD r)))⁻¹ ∈
        Hh hsw) ∧
    wInH (CFSG.KD.B4A.RW r) = true :=
  st_sound_bdd st_fold (by norm_num) (fun r _ => rw_len r) pw_len pw_ok (Hh hsw) xG (u hsw)
    (fun c _ => ⟨_, rfl⟩)
    (fun c => by rw [xG, ← map_mul, yGen_mul_self, map_one]) (u_mul_self hsw)
    (fun c hc h7 => by rw [data_ok.2.2.2.1 c hc h7, xG, xG, u_conj hsw hc h7])
    (rel47 hsw)
    (fun w hw h => by
      change wVal xG w = 1
      rw [wVal_xG, psiG, MonoidHom.comp_apply, isOne_psi hw h, map_one])

theorem ker_rho_le_psiG : rho432F.ker ≤ (psiG hsw).ker := by
  intro y hy
  rw [MonoidHom.mem_ker, psiG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (ker_rho432F_le_ker_psi hy),
    map_one]

theorem relIndex_map_eq {E G : Type*} [Group E] [Group G] (f : E →* G) (P : Subgroup E) :
    (P.map f).relIndex f.range = (P ⊔ f.ker).index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]

theorem relIndex_le (P : Subgroup (YGroup 4 3 2)) {m : ℕ} (hm0 : 0 < m)
    (hm : m ≤ Nat.card (P.map rho432F)) :
    (P.map (psiG hsw)).relIndex (psiG hsw).range ≤ 4089470473293004800 / m := by
  have hfin := finite_y432
  rw [relIndex_map_eq]
  have h1 : (P ⊔ (psiG hsw).ker).index ≤ (P ⊔ rho432F.ker).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le (sup_le_sup_left ker_rho_le_psiG P))
  refine h1.trans ?_
  rw [← relIndex_map_eq]
  have hle : P.map rho432F ≤ rho432F.range := by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  have h2 := Subgroup.card_mul_index ((P.map rho432F).subgroupOf rho432F.range)
  have h3 : Nat.card ((P.map rho432F).subgroupOf rho432F.range) = Nat.card (P.map rho432F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h3, card_range_rho432F] at h2
  rw [Subgroup.relIndex, ← h2]
  rw [Nat.le_div_iff_mul_le hm0]
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ hm

end

@[expose] def nodeAt (i : Fin 46) : ℕ := liveL.getD i 0

@[expose] def idxOf (n : ℕ) : Fin 46 := if h : liveL.idxOf n < 46 then ⟨_, h⟩ else ⟨0, by norm_num⟩

theorem nodeAt_mem (i : Fin 46) : nodeAt i ∈ liveL := by
  unfold nodeAt
  rw [List.getD_eq_getElem _ _ (by rw [liveL_len]; exact i.2)]
  exact List.getElem_mem _

theorem nodeAt_idxOf {n : ℕ} (hn : n ∈ liveL) : nodeAt (idxOf n) = n := by
  have hlt : liveL.idxOf n < 46 := by rw [← liveL_len]; exact List.idxOf_lt_length_iff.2 hn
  unfold idxOf nodeAt
  rw [dif_pos hlt]
  simp only
  rw [List.getD_eq_getElem _ _ (by rw [liveL_len]; exact hlt), List.getElem_idxOf]

theorem live_lt {n : ℕ} (h : 0 < CFSG.KD.B4AN.LIVE &&& (1 <<< n)) : n < 64 := by
  by_contra hn
  have hb : (CFSG.KD.B4AN.LIVE).testBit n = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (by unfold CFSG.KD.B4AN.LIVE; norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 64 ≤ n)))
  rw [Nat.one_shiftLeft, Nat.and_two_pow, hb] at h
  exact absurd h (by simp)

theorem live_mem {n : ℕ} (h : 0 < CFSG.KD.B4AN.LIVE &&& (1 <<< n)) : n ∈ liveL :=
  (liveL_spec n).2 ⟨live_lt h, (live_iff n).1 h⟩

theorem gens_stab : ∀ j < 64, liveB j = true → ∀ t < CFSG.KD.B4AN.GN j,
    isStab (dKind (CFSG.KD.B4A.RD (genOf CFSG.KD.B4AN.GS j t))) = true ∧
      dN2 (CFSG.KD.B4A.RD (genOf CFSG.KD.B4AN.GS j t)) = j := by
  decide +kernel

theorem sum_ok : ∑ i : Fin 46, 4089470473293004800 / CFSG.KD.B4AC.MJ (nodeAt i) = 2031941058560000 := by
  decide +kernel

section

@[expose] noncomputable def Xn : ℕ → Ghat hsw := Classical.choose facts

theorem Xn_zero : Xn 0 = 1 := (Classical.choose_spec facts).1

theorem Xn_facts : ∀ r < 5965,
    (isFact (dKind (CFSG.KD.B4A.RD r)) = true →
      Xn (dN1 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.PW (dPt (CFSG.KD.B4A.RD r))) * u hsw *
        (Xn (dN2 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.RW r))⁻¹ ∈ Hh hsw) ∧
    (isStab (dKind (CFSG.KD.B4A.RD r)) = true →
      Xn (dN2 (CFSG.KD.B4A.RD r)) * wVal xG (CFSG.KD.B4A.RW r) * (Xn (dN2 (CFSG.KD.B4A.RD r)))⁻¹ ∈
        Hh hsw) ∧
    wInH (CFSG.KD.B4A.RW r) = true := (Classical.choose_spec facts).2

theorem stab_conj {n g : ℕ} (hs : isStab (dKind (CFSG.KD.B4A.RD g)) = true)
    (hn : dN2 (CFSG.KD.B4A.RD g) = n) :
    Xn n * psiG hsw (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW g)) * (Xn n)⁻¹ ∈ Hh hsw := by
  rw [RD_per] at hs hn
  rw [RW_per]
  have hg : g % 8192 < 8192 := Nat.mod_lt _ (by norm_num)
  have h5 : g % 8192 < 5965 := by
    by_contra h
    rw [RD_tail _ hg (by omega)] at hs
    exact absurd hs (by decide)
  have := (Xn_facts _ h5).2.1 hs
  rw [hn, wVal_xG] at this
  exact this

@[expose] noncomputable def Sn (i : Fin 46) : Subgroup (Ghat hsw) := (nodeSub (nodeAt i)).map (psiG hsw)

@[expose] noncomputable def repN (i : Fin 46) : Set (Ghat hsw) :=
  {k | ∃ e < CFSG.KD.B4AN.RN (nodeAt i),
    entryOK CFSG.KD.B4A.RD CFSG.KD.B4AN.LIVE (nodeAt i) (rootE (nodeAt i) e) = true ∧
    k = psiG hsw (wVal (yGen 4 3 2) (CFSG.KD.B4A.PW (dPt (CFSG.KD.B4A.RD (rootE (nodeAt i) e)))))}

open Classical in
@[expose] noncomputable def tgtN (i : Fin 46) (k : Ghat hsw) : Fin 46 :=
  if h : k ∈ repN i then idxOf (dN2 (CFSG.KD.B4A.RD (rootE (nodeAt i) (Classical.choose h))))
  else idxOf 0

open Classical in
@[expose] noncomputable def tgtEltN (i : Fin 46) (k : Ghat hsw) : Ghat hsw :=
  if h : k ∈ repN i then
    psiG hsw (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (rootE (nodeAt i) (Classical.choose h))))
  else 1

theorem entry_spec {j e : ℕ} (h : entryOK CFSG.KD.B4A.RD CFSG.KD.B4AN.LIVE j e = true) :
    isFact (dKind (CFSG.KD.B4A.RD e)) = true ∧ dN1 (CFSG.KD.B4A.RD e) = j ∧
      0 < CFSG.KD.B4AN.LIVE &&& (1 <<< dN2 (CFSG.KD.B4A.RD e)) := by
  unfold entryOK at h
  rw [sB_eq] at h
  simp only [andB_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.blt_eq.mp h.2.2⟩

theorem T_le : Y442Tw.lsub CertificateChecks.KernelY442.yL ≤ T432 := by
  rw [Y442Tw.lsub, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  refine Subgroup.subset_closure ⟨c, ?_, rfl⟩
  simp only [CertificateChecks.KernelY442.yL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[expose] noncomputable def twist : TwistData (Hh hsw) (Th hsw) (u hsw) 46 where
  x i := Xn (nodeAt i)
  S := Sn
  rep := repN
  tgt := tgtN
  tgtElt := tgtEltN
  base := idxOf 0
  base_mem := by
    rw [nodeAt_idxOf ((liveL_spec 0).2 ⟨by norm_num, by decide⟩), Xn_zero]
    exact (Hh hsw).one_mem
  S_le i := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  S_conj i := by
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨g, ⟨hs, hn⟩, rfl⟩ := hz
      exact stab_conj hs hn
    | one => rw [map_one, mul_one, mul_inv_cancel]; exact (Hh hsw).one_mem
    | mul a b _ _ ha hb =>
      have e : Xn (nodeAt i) * psiG hsw (a * b) * (Xn (nodeAt i))⁻¹ =
          (Xn (nodeAt i) * psiG hsw a * (Xn (nodeAt i))⁻¹) *
            (Xn (nodeAt i) * psiG hsw b * (Xn (nodeAt i))⁻¹) := by
        rw [map_mul]; group
      rw [e]
      exact (Hh hsw).mul_mem ha hb
    | inv a _ ha =>
      have e : Xn (nodeAt i) * psiG hsw a⁻¹ * (Xn (nodeAt i))⁻¹ =
          (Xn (nodeAt i) * psiG hsw a * (Xn (nodeAt i))⁻¹)⁻¹ := by
        rw [map_inv]; group
      rw [e]
      exact (Hh hsw).inv_mem ha
  rep_le i := by
    rintro _ ⟨e, -, -, rfl⟩
    exact ⟨_, rfl⟩
  rep_cover i := by
    rintro _ ⟨y, rfl⟩
    have hmem := nodeAt_mem i
    obtain ⟨hj, hl⟩ := (liveL_spec _).1 hmem
    obtain ⟨e, he, hent, z, hz, t, ht, hy⟩ := cover_y hj ((live_iff _).2 hl) y
    refine ⟨_, ⟨e, he, hent, rfl⟩, psiG hsw z, ⟨z, ?_, rfl⟩, psiG hsw t, ⟨t, T_le ht, rfl⟩, ?_⟩
    · refine (Subgroup.closure_le _).2 ?_ hz
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.subset_closure ⟨_, gens_stab _ hj hl s hs, rfl⟩
    · rw [psiG, MonoidHom.comp_apply, hy, map_mul, map_mul]
      rfl
  tgtElt_mem i k hk := by
    unfold tgtEltN
    rw [dif_pos hk]
    exact ⟨_, rfl⟩
  tgt_spec i k hk := by
    unfold tgtN tgtEltN
    rw [dif_pos hk, dif_pos hk]
    obtain ⟨he, hent, hk'⟩ := Classical.choose_spec hk
    set e := Classical.choose hk
    have hmem := nodeAt_mem i
    obtain ⟨hj, hl⟩ := (liveL_spec _).1 hmem
    obtain ⟨hf, h1, h2⟩ := entry_spec hent
    have hr : rootE (nodeAt i) e < 5965 := data_ok.1 _ hj hl e he
    have := (Xn_facts _ hr).1 hf
    rw [nodeAt_idxOf (live_mem h2)]
    rw [h1, wVal_xG, wVal_xG, ← hk'] at this
    exact this

theorem index_Hh : (Hh hsw).index ≤ 2031941058560000 := by
  have hfin := finite_y432
  have : Finite (Hh hsw) := Finite.of_surjective (psiG hsw).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨-, h⟩ := (twist).index_le_sum (u_mul_self hsw) (u_conj_Th hsw) (closure_Hh_u hsw)
  refine h.trans ?_
  rw [← sum_ok]
  refine Finset.sum_le_sum fun i _ => ?_
  have hmem := nodeAt_mem i
  obtain ⟨hj, hl⟩ := (liveL_spec _).1 hmem
  obtain ⟨hm0, -⟩ := data_ok.2.1 _ hj hl
  exact relIndex_le _ hm0 (node_card hj hl)

theorem B433_finite_card_le :
    Finite B433 ∧ Nat.card B433 ≤ 4154781481226426191177580544000000 := by
  have hfin := finite_y432
  have hHcard : Nat.card (Hh hsw) ≤ 4089470473293004800 := by
    rw [card_Hh]
    exact card_range_psi_le
  have hidx := index_Hh
  have hGne : Nat.card (Ghat hsw) ≠ 0 := by
    have : Finite (Hh hsw) := Finite.of_surjective (psiG hsw).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
    have hfi : (Hh hsw).FiniteIndex :=
      ((twist).index_le_sum (u_mul_self hsw) (u_conj_Th hsw) (closure_Hh_u hsw)).1
    rw [← Subgroup.card_mul_index (Hh hsw)]
    exact Nat.mul_ne_zero Nat.card_pos.ne' hfi.index_ne_zero
  have hG : Nat.card (Ghat hsw) ≤ 4089470473293004800 * 2031941058560000 := by
    rw [← Subgroup.card_mul_index (Hh hsw)]
    exact Nat.mul_le_mul hHcard hidx
  have hGfin : Finite (Ghat hsw) := Nat.finite_of_card_ne_zero hGne
  refine ⟨Finite.of_injective _ (SemidirectProduct.inl_injective (φ := act hsw)), ?_⟩
  rw [card_Ghat] at hG
  omega

end

end CertificateChecks.KernelB433

end

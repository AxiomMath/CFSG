module

public import Certificates.Kernel.B433Alt.Exact
public import Certificates.Kernel.B433Alt.Lab
public import CFSG.Certificates.Kernel.B433Alt.LabSound
public import CFSG.YGroups.DCE.B433Y333

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CFSG.YGroups.DCE.B433 CFSG.Certificates.TwDce CFSG.YGroups.SymGen

#kc_forall_tree lab_all (fun i => CFSG.KD.B4AL.labChk i = true) 8 CFSG.KD.B4AL.lab

theorem lab_data : (∀ i < 8, liveB (CFSG.KD.B4AL.LN.getD i 0) = true ∧
      CFSG.KD.B4AT.PA.getD (CFSG.KD.B4AL.LN.getD i 0) 0 = 0 ∧ CFSG.KD.B4AL.LN.getD i 0 < 64) ∧
    ((List.range 8).map fun i => CFSG.KD.B4AL.LN.getD i 0).Nodup ∧
    (∀ i < 8, ∀ c ∈ CFSG.KD.B4AL.LW.getD i [], c ≤ 10 ∧ c ≠ 4) ∧
    31671 * 1185415168 ≤ ((List.range 8).map fun i =>
      vN (idxOf (CFSG.KD.B4AL.LN.getD i 0)) * CFSG.KD.B4AL.LO.getD i 0).sum := by
  decide +kernel

theorem lsub_tL_eq : CFSG.YGroups.Y442Tw.lsub CertificateChecks.KernelY442.tL = J432 := by
  rw [CFSG.YGroups.Y442Tw.lsub, J432]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, CertificateChecks.KernelY442.tL, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide, rfl⟩
  · rintro ⟨c, ⟨hc, hc4⟩, rfl⟩
    exact ⟨c, by omega, rfl⟩

section

@[expose] noncomputable def PG : Subgroup (Ghat hsw) := P333.map SemidirectProduct.inl

theorem trGen_mem_P {w : List ℕ} (hw : ∀ c ∈ w, c ≤ 10 ∧ c ≠ 4) :
    evalWord (trGen xG (u hsw)) w ∈ PG := by
  induction w with
  | nil => exact PG.one_mem
  | cons c w ih =>
    rw [evalWord_cons]
    refine PG.mul_mem ?_ (ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨hc, hc4⟩ := hw c List.mem_cons_self
    rcases Nat.lt_or_ge c 10 with h | h
    · rw [trGen_lt h]
      exact ⟨_, map_J432_le_P333 ⟨_, Subgroup.subset_closure ⟨c, ⟨h, hc4⟩, rfl⟩, rfl⟩, rfl⟩
    · have h10 : c = 10 := by omega
      subst h10
      rw [trGen_ten]
      exact ⟨tB, tB_mem_P333, rfl⟩

@[expose] noncomputable def setupG : SymGen.Setup (Ghat hsw) (YGroup 4 3 2) Unit where
  t := 1
  ψ := psiG hsw
  o := ()
  w := fun _ => 1
  t_mul_t := mul_one 1
  w_smul := fun _ => rfl
  stab_comm := fun c _ => by rw [mul_one, one_mul]

theorem setupG_H : setupG.H = Hh hsw := rfl

theorem stab_mem {j g : ℕ} (h : stabAt CFSG.KD.B4A.RD (nat_lit 5965) g j = true) :
    wVal (yGen 4 3 2) (CFSG.KD.B4A.RW g) ∈ CFSG.YGroups.DCE.B.stabSub setupG (Xn j) := by
  unfold stabAt at h
  rw [sB_eq] at h
  simp only [andB_iff] at h
  obtain ⟨hg, hs, hj⟩ := h
  rw [CFSG.YGroups.DCE.B.mem_stabSub]
  have := (Xn_facts g (Nat.blt_eq.mp hg)).2.1 hs
  rw [Nat.eq_of_beq_eq_true hj, wVal_xG] at this
  exact this

theorem stabsAt_spec {j G nG : ℕ} (h : stabsAt CFSG.KD.B4A.RD (nat_lit 5965) G nG j = true) :
    ∀ k < nG, stabAt CFSG.KD.B4A.RD (nat_lit 5965) (fld G (20 * k) (ones 20)) j = true := by
  induction nG with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    change andB (stabsAt CFSG.KD.B4A.RD (nat_lit 5965) G n j)
      (stabAt CFSG.KD.B4A.RD (nat_lit 5965) (fld G (Nat.mul 20 n) (ones 20)) j) = true at h
    rw [andB_iff] at h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h.1 k hk
    · exact h.2

theorem card_P333_ge (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    153064959367549707878400 ≤ Nat.card P333 := by
  classical
  have hfinB : Finite B433 := (B433_finite_card_le).1
  have hfinG := finite_Ghat
  have hfinY := finite_y432
  let inst : MulAction (YGroup 4 3 2) (Fin 31671) := MulAction.compHom (Fin 31671) rho432F
  have hsmul : ∀ (e : YGroup 4 3 2) (y : Fin 31671), e • y = rho432F e y := fun _ _ => rfl
  obtain ⟨hex2, hHeq, hex3⟩ := exact hG
  obtain ⟨hlv, hnd, hw, hsum⟩ := lab_data
  have hJ : ∀ e : YGroup 4 3 2, e • (0 : Fin 31671) = 0 → setupG.ψ e ∈ PG := by
    intro e he
    have hJe : e ∈ J432 := by
      rw [← lsub_tL_eq]
      exact CertificateChecks.KernelY442.stab_zero he
    exact ⟨psi e, map_J432_le_P333 ⟨e, hJe, rfl⟩, rfl⟩
  have hlab : ∀ i < 8,
      trOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW (nat_lit 5965)
        (nat_lit 0) (nat_lit 0) (CFSG.KD.B4AL.LW.getD i []) (CFSG.KD.B4AL.LJ.getD i 0)
        (CFSG.KD.B4AL.LN.getD i 0) (CFSG.KD.B4AL.LA.getD i 0) = true ∧
      wInH (CFSG.KD.B4AL.LA.getD i 0) = true ∧ CFSG.KD.B4AL.LPt.getD i 0 < 31671 ∧
      ev1 CFSG.KD.B4A.LP (CFSG.KD.B4AL.LA.getD i 0) 0 = CFSG.KD.B4AL.LPt.getD i 0 ∧
      orbCount (orbChunks CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW (fun _ => 0) (fun _ => 0)
        (CFSG.KD.B4AL.LN.getD i 0) 0 (CFSG.KD.B4AL.LG.getD i 0) (CFSG.KD.B4AL.LNG.getD i 0)
        (CFSG.KD.B4AL.LC.getD i []) (orbInit (CFSG.KD.B4AL.LPt.getD i 0))) =
          CFSG.KD.B4AL.LO.getD i 0 ∧
      stabsAt CFSG.KD.B4A.RD (nat_lit 5965) (CFSG.KD.B4AL.LG.getD i 0)
        (CFSG.KD.B4AL.LNG.getD i 0) (CFSG.KD.B4AL.LN.getD i 0) = true := by
    intro i hi
    have h := lab_all i hi
    unfold CFSG.KD.B4AL.labChk labOK at h
    simp only [andB_iff] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, h6⟩
  have hidx : ∀ i < 8, nodeAt (idxOf (CFSG.KD.B4AL.LN.getD i 0)) = CFSG.KD.B4AL.LN.getD i 0 ∧
      idxOf (CFSG.KD.B4AL.LN.getD i 0) ∈ Ev := by
    intro i hi
    obtain ⟨hl, hp, h64⟩ := hlv i hi
    have hn := nodeAt_idxOf ((liveL_spec _).2 ⟨h64, hl⟩)
    refine ⟨hn, ?_⟩
    rw [Ev, Finset.mem_filter, hn]
    exact ⟨Finset.mem_univ _, hp⟩
  have hpt : ∀ i < 8, (Fin.ofNat 31671 (CFSG.KD.B4AL.LPt.getD i 0)) =
      wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0) • (0 : Fin 31671) := by
    intro i hi
    obtain ⟨-, hwa, hlt, hev1, -, -⟩ := hlab i hi
    apply Fin.ext
    rw [hsmul]
    change _ = ((rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0))) ⟨0, by norm_num⟩ : ℕ)
    rw [ev1_spec tables hwa (by norm_num : (0 : ℕ) < 31671), Fin.val_ofNat,
      Nat.mod_eq_of_lt hlt]
    exact hev1.symm
  have hgen : ∀ i < 8, genSub CFSG.KD.B4A.RW (CFSG.KD.B4AL.LG.getD i 0)
      (CFSG.KD.B4AL.LNG.getD i 0) ≤
      CFSG.YGroups.DCE.B.stabSub setupG (Xn (CFSG.KD.B4AL.LN.getD i 0)) := by
    intro i hi
    obtain ⟨-, -, -, -, -, hst⟩ := hlab i hi
    rw [genSub, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact stab_mem (stabsAt_spec hst k k.2)
  let labs : List (ℕ × Fin 31671) := (List.range 8).map fun i =>
    (CFSG.KD.B4AL.LN.getD i 0, (Fin.ofNat 31671 (CFSG.KD.B4AL.LPt.getD i 0)))
  have hmemlabs : ∀ lab ∈ labs, ∃ i < 8,
      lab = (CFSG.KD.B4AL.LN.getD i 0, (Fin.ofNat 31671 (CFSG.KD.B4AL.LPt.getD i 0))) := by
    intro lab hlab'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hlab'
    exact ⟨i, List.mem_range.1 hi, rfl⟩
  have hmain := Setup.sum_le_ncard_porb (S := setupG) (P := PG) (ω₀ := (0 : Fin 31671))
    Xn labs (by rw [List.map_map]; exact hnd)
    (by
      intro lab hl lab' hl' a b hab
      obtain ⟨i, hi, rfl⟩ := hmemlabs lab hl
      obtain ⟨i', hi', rfl⟩ := hmemlabs lab' hl'
      obtain ⟨hι, hιE⟩ := hidx i hi
      obtain ⟨hι', hιE'⟩ := hidx i' hi'
      rw [Setup.cosetOf, Setup.cosetOf, QuotientGroup.eq] at hab
      set ι := idxOf (CFSG.KD.B4AL.LN.getD i 0)
      set ι' := idxOf (CFSG.KD.B4AL.LN.getD i' 0)
      have hxι : (twist).x ι = Xn (CFSG.KD.B4AL.LN.getD i 0) := by
        change Xn (nodeAt ι) = _
        rw [hι]
      have hxι' : (twist).x ι' = Xn (CFSG.KD.B4AL.LN.getD i' 0) := by
        change Xn (nodeAt ι') = _
        rw [hι']
      have hx : (twist).x ι' = (Xn (CFSG.KD.B4AL.LN.getD i 0) * (setupG.ψ a)⁻¹ * setupG.ψ b *
          (Xn (CFSG.KD.B4AL.LN.getD i' 0))⁻¹)⁻¹ * (twist).x ι * (setupG.ψ (a⁻¹ * b)) := by
        rw [hxι, hxι', map_mul, map_inv]
        group
      have hz : Xn (CFSG.KD.B4AL.LN.getD i 0) * (setupG.ψ a)⁻¹ * setupG.ψ b *
          (Xn (CFSG.KD.B4AL.LN.getD i' 0))⁻¹ ∈ Hh hsw := by
        have e : ((setupG.ψ a * (Xn (CFSG.KD.B4AL.LN.getD i 0))⁻¹)⁻¹ *
            (setupG.ψ b * (Xn (CFSG.KD.B4AL.LN.getD i' 0))⁻¹)) =
            Xn (CFSG.KD.B4AL.LN.getD i 0) * (setupG.ψ a)⁻¹ * setupG.ψ b *
              (Xn (CFSG.KD.B4AL.LN.getD i' 0))⁻¹ := by group
        rw [← e]
        exact hab
      have := hex2 ι hιE ι' hιE' ⟨_, (Hh hsw).inv_mem hz, _, ⟨a⁻¹ * b, rfl⟩, hx⟩
      change CFSG.KD.B4AL.LN.getD i 0 = CFSG.KD.B4AL.LN.getD i' 0
      rw [← hι, ← hι', this])
    (by
      intro lab hl
      obtain ⟨i, hi, rfl⟩ := hmemlabs lab hl
      obtain ⟨htrOK, -, -, -, -, -⟩ := hlab i hi
      have htr' := tr_fact htrOK
      have hw0 : wVal xG 0 = 1 := rfl
      rw [Xn_zero, hw0, one_mul, one_mul, wVal_xG] at htr'
      refine Setup.fib_subset_porb hJ
        (e₀ := (wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0))⁻¹) ?_ ?_
      · rw [inv_inv, ← hpt i hi]
        exact MulAction.mem_orbit_self _
      · refine ⟨(evalWord (trGen xG (u hsw)) (CFSG.KD.B4AL.LW.getD i []))⁻¹,
          PG.inv_mem (trGen_mem_P (hw i hi)), ?_⟩
        rw [Setup.cosetOf, QuotientGroup.eq]
        have e : (setupG.ψ (wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0))⁻¹ *
            (Xn (CFSG.KD.B4AL.LN.getD i 0))⁻¹)⁻¹ *
            (evalWord (trGen xG (u hsw)) (CFSG.KD.B4AL.LW.getD i []))⁻¹ =
            (evalWord (trGen xG (u hsw)) (CFSG.KD.B4AL.LW.getD i []) *
              (Xn (CFSG.KD.B4AL.LN.getD i 0) *
                psiG hsw (wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0)))⁻¹)⁻¹ := by
          change ((psiG hsw) (wVal (yGen 4 3 2) (CFSG.KD.B4AL.LA.getD i 0))⁻¹ *
            (Xn (CFSG.KD.B4AL.LN.getD i 0))⁻¹)⁻¹ * _ = _
          rw [map_inv]
          group
        rw [e]
        exact (Hh hsw).inv_mem htr')
    (fun j => vN (idxOf j))
    (by
      intro lab hl
      obtain ⟨i, hi, rfl⟩ := hmemlabs lab hl
      obtain ⟨hι, hιE⟩ := hidx i hi
      have hle := hex3 _ hιE
        ((CFSG.YGroups.DCE.B.stabSub setupG (Xn (CFSG.KD.B4AL.LN.getD i 0))).map (psiG hsw))
        (by
          rintro _ ⟨e, he, rfl⟩
          change Xn (nodeAt _) * _ * (Xn (nodeAt _))⁻¹ ∈ _
          rw [hι]
          exact (CFSG.YGroups.DCE.B.mem_stabSub _ _ _).1 he)
      exact hle.trans (relIndex_map_range_le (psiG hsw) _))
    (by
      intro lab hl
      obtain ⟨i, hi, rfl⟩ := hmemlabs lab hl
      exact ⟨_, (hpt i hi).symm⟩)
  have hlow : ((List.range 8).map fun i =>
      vN (idxOf (CFSG.KD.B4AL.LN.getD i 0)) * CFSG.KD.B4AL.LO.getD i 0).sum ≤
      (labs.map fun lab => vN (idxOf lab.1) *
        (MulAction.orbit (CFSG.YGroups.DCE.B.stabSub setupG (Xn lab.1)) lab.2).ncard).sum := by
    rw [List.map_map]
    refine List.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
    have hi' := List.mem_range.1 hi
    obtain ⟨-, -, hlt, -, horbi, -⟩ := hlab i hi'
    refine (orbChunks_sound tables rw_stab hlt horbi).trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro y ⟨k, hk, rfl⟩
    refine ⟨⟨k, hgen i hi' hk⟩, ?_⟩
    change rho432F k _ = rho432F k ⟨_, hlt⟩
    congr 1
    apply Fin.ext
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt hlt]
  have horbE : (MulAction.orbit (YGroup 4 3 2) (0 : Fin 31671)).ncard ≤ 31671 :=
    (Set.ncard_le_card _).trans (by rw [Nat.card_fin])
  rw [Setup.ncard_porb, setupG_H] at hmain
  have hidxP : 1185415168 ≤ (Hh hsw).relIndex PG := by
    have h := (hsum.trans hlow).trans (hmain.trans (Nat.mul_le_mul_right _ horbE))
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hJmap : J432.map (psiG hsw) ≤ Hh hsw ⊓ PG :=
    le_inf (Subgroup.map_le_range _ _) (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨psi e, map_J432_le_P333 ⟨e, he, rfl⟩, rfl⟩)
  have hJidx : J432.index ≤ 31671 := by
    rw [← lsub_tL_eq]
    exact CertificateChecks.KernelY442.index_tL_le.2
  have hJcard : 129123503308800 ≤ Nat.card (J432.map (psiG hsw)) := by
    have hrel := (relIndex_map_range_le (psiG hsw) J432).trans hJidx
    have hmul := Subgroup.relIndex_mul_card (H := J432.map (psiG hsw)) (K := Hh hsw)
    have hle' : J432.map (psiG hsw) ≤ Hh hsw := Subgroup.map_le_range _ _
    rw [inf_of_le_left hle', hHeq] at hmul
    have : 4089470473293004800 ≤ 31671 * Nat.card (J432.map (psiG hsw)) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hrel
    omega
  have hPcard := Subgroup.relIndex_mul_card (H := Hh hsw) (K := PG)
  have hPG : Nat.card PG = Nat.card P333 := Subgroup.card_map_of_injective inlB_injective
  rw [← hPG, ← hPcard]
  calc 153064959367549707878400 = 1185415168 * 129123503308800 := by norm_num
    _ ≤ (Hh hsw).relIndex PG * Nat.card (J432.map (psiG hsw)) := Nat.mul_le_mul hidxP hJcard
    _ ≤ (Hh hsw).relIndex PG * Nat.card (Hh hsw ⊓ PG :) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hJmap)

end

end CertificateChecks.KernelB433

end

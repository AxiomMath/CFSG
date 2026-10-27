module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Aut
public import CFSG.Quasithin.Background.Harris.R1.D4VertModel
public import CFSG.Quasithin.Background.Harris.R1.D4VertPres
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverB
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocV
public import Certificates.Certificate300207

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2.Native CFSG.Quasithin CFSG.Quasithin.D4Hex CFSG.CosetTable
  CFSG.Quasithin.Background.Harris.R1.J2Vert
open CFSG.Monster.B.Co2 (allLt_spec)

@[expose] noncomputable def x0D : D := d4Word (hWords.getD 1 [])

@[expose] noncomputable def aD : D := d4Word (hWords.getD 2 [])

@[expose] noncomputable def bD : D := d4Word (hWords.getD 3 [])

theorem hWords_lt_nat {i : ℕ} (hi : i < 4) : ∀ k ∈ hWords.getD i [], k < 8 := by
  interval_cases i <;> decide

theorem gd_x0 : Gd x0A x0D := gd_word (hWords_lt_nat (by norm_num))

theorem hWords_zero_eq : d4Word (hWords.getD 0 []) = d4z := rfl

theorem y1D_mem_U : y1D ∈ d4U := d4Word_mem_U _ (by decide)

theorem y2D_mem_U : y2D ∈ d4U := d4Word_mem_U _ (by decide)

theorem r0D_mem_U : r0D ∈ d4U := d4Word_mem_U _ (by decide)

theorem y1D_mem_B : y1D ∈ d4B := d4U_le_d4B y1D_mem_U

theorem y2D_mem_B : y2D ∈ d4B := d4U_le_d4B y2D_mem_U

theorem r0D_mem_B : r0D ∈ d4B := d4U_le_d4B r0D_mem_U

theorem zeD_mem_B : zeD ∈ d4B :=
  d4Zeta_mem_B

theorem ptArr_eq (w : List ℕ) : ptArr w = d4WordArr w := rfl

theorem mem_d4H_of_fixPt {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : fixPt w = true) : d4Word w ∈ d4H := by
  simp only [fixPt, beq_iff_eq, ptArr_eq] at h
  exact mem_d4H_of_rep (rep_d4WordArr w hw) h

theorem mem_d4N_of_fixLine {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : fixLine w = true) : d4Word w ∈ d4N := by
  simp only [fixLine, ptArr_eq] at h
  exact mem_d4N_of_rep (rep_d4WordArr w hw) h

theorem not_mem_d4H_of_movePt {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : movePt w = true) : d4Word w ∉ d4H := by
  simp only [movePt, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, ptArr_eq] at h
  intro hH
  apply h
  have h0 := (mem_d4H_iff_act _).1 hH
  have h1 := (rep_d4WordArr w hw) pt0
  rw [h0] at h1
  exact h1

theorem s0D_mem_N : s0D ∈ d4N := by
  obtain ⟨h, -⟩ := Certificates.certificate300207
  exact mem_d4N_of_fixLine (nWords_lt_nat (by norm_num)) h

theorem s0D_not_mem_H :
    s0D ∉ d4H := by
  obtain ⟨-, h, -⟩ := Certificates.certificate300207
  exact not_mem_d4H_of_movePt (nWords_lt_nat (by norm_num)) h

theorem aD_mem_H : aD ∈ d4H := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate300207
  exact mem_d4H_of_fixPt (hWords_lt_nat (by norm_num)) h

theorem bD_mem_H : bD ∈ d4H := by
  obtain ⟨-, -, -, h, -⟩ := Certificates.certificate300207
  exact mem_d4H_of_fixPt (hWords_lt_nat (by norm_num)) h

theorem x0D_eq_vB : x0D = vB := by
  obtain ⟨-, -, -, -, h, -⟩ := Certificates.certificate300207
  simp only [x0IsVB, beq_iff_eq] at h
  rw [← cz_eq] at h
  exact (Gd.eq_iff gd_x0 ⟨repE_vB, validR_vB⟩).1 h

theorem card_d4H :
    Nat.card d4H = 258048 := by
  have h1 := MulAction.index_stabilizer D pt0
  have horb : MulAction.orbit D pt0 = Set.univ :=
    Set.eq_univ_of_forall fun i => MulAction.mem_orbit_iff.2 (exists_smul_pt0_eq i)
  have hst : MulAction.stabilizer D pt0 = d4H := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_d4H_iff]
  rw [horb, Set.ncard_univ, hst, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := Subgroup.card_mul_index d4H
  rw [h1, card_trialityGroup8] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 819) (h2.trans (by norm_num))

theorem card_d4N :
    Nat.card d4N = 86016 := by
  have h1 := MulAction.index_stabilizer D (0 : Fin 2457)
  have horb : MulAction.orbit D (0 : Fin 2457) = Set.univ := by
    refine Set.eq_univ_of_forall fun l => MulAction.mem_orbit_iff.2 ?_
    obtain ⟨g, hg⟩ := exists_smul_flag0_eq (⟨(lpt0 l, l), by simp [mem_lineSet_iff, lpt0]⟩ : Flag)
    refine ⟨g, ?_⟩
    have := congrArg (fun x : Flag => x.1.2) hg
    simpa [smul_flag_snd, flag0_snd] using this
  have hst : MulAction.stabilizer D (0 : Fin 2457) = d4N := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_d4N_iff, smul_line_zero_iff]
  rw [horb, Set.ncard_univ, hst, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := Subgroup.card_mul_index d4N
  rw [h1, card_trialityGroup8] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2457) (h2.trans (by norm_num))

theorem card_closure_of_tab {S : Set D} {gs gi : Array (Array ℕ)} {pl : List (ℕ × ℕ)} {N : ℕ}
    (hgood : ∀ x ∈ gs, ∃ σ ∈ Subgroup.closure S, Gd x σ)
    (hS : ∀ σ ∈ S, ∃ i < gs.size, RepE d4E gs[i]! σ) (h : tabOK gs gi pl N = true) :
    Nat.card (Subgroup.closure S) = N := by
  have hon : tabOKOn gs gi (buildTabR gs pl) (lookup (mkIdx (buildTabR gs pl))) N = true := h
  obtain ⟨hsize, hidx, -, -⟩ := tabOKOn_parts hon
  rw [card_eq_of_tab (good_buildTabR hgood pl) hidx
    (tab_complete_R hS (oneR_mem_buildTabR _ _) hon), hsize]

theorem zeD_conj_mem_U {u : D} (hu : u ∈ d4U) :
    zeD * u * zeD⁻¹ ∈ d4U := by
  obtain ⟨-, -, -, -, -, h, -⟩ := Certificates.certificate300207
  simp only [zetaConjOK, List.all_eq_true, beq_iff_eq, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h6⟩ := h
  have key : ∀ (j : ℕ) (hj : j < 8) (w : List ℕ) (hw : ∀ k ∈ w, k < 8),
      mulR zA d4Gens[j]! = mulR (wordR d4Gens w) zA → zeD * d4GenG j * zeD⁻¹ = d4Word w := by
    intro j hj w hw h
    have hg : Gd d4Gens[j]! (d4GenG j) := ⟨repE_d4Gens hj, validR_d4Gens hj⟩
    have := (Gd.eq_iff (gd_z.mul hg) ((gd_word hw).mul gd_z)).1 h
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hz0 := key 0 (by norm_num) [2] (by decide) h0
  have hz1 := key 1 (by norm_num) [0, 1] (by decide) h1
  have hz2 := key 2 (by norm_num) [1, 2] (by decide) h2
  have hz6 := key 6 (by norm_num) [0, 2, 6, 0, 2] (by decide) h6
  have hmem : d4U ≤ d4U.comap (MulAut.conj zeD).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 4 := hk
    show zeD * uGH k * zeD⁻¹ ∈ d4U
    interval_cases k
    · show zeD * d4GenG 0 * zeD⁻¹ ∈ d4U
      rw [hz0]; exact d4Word_mem_U _ (by decide)
    · show zeD * d4GenG 1 * zeD⁻¹ ∈ d4U
      rw [hz1]; exact d4Word_mem_U _ (by decide)
    · show zeD * d4GenG 2 * zeD⁻¹ ∈ d4U
      rw [hz2]; exact d4Word_mem_U _ (by decide)
    · show zeD * d4GenG 6 * zeD⁻¹ ∈ d4U
      rw [hz6]; exact d4Word_mem_U _ (by decide)
  exact hmem hu

theorem cj_mem_U (i : ℕ) {u : D} (hu : u ∈ d4U) :
    cj i u ∈ d4U := by
  induction i with
  | zero => simpa [cj] using hu
  | succ i ih =>
    rw [← cj_succ]
    exact zeD_conj_mem_U ih

theorem Q2_le_d4U : Q2 ≤ d4U := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  by_cases h : i.val < 7
  · rw [gQ_lt h]; exact cj_mem_U _ y1D_mem_U
  · rw [gQ_ge h]; exact cj_mem_U _ y2D_mem_U

section CertQ2

theorem gd_z0 : Gd z0R d4z := ⟨repE_z0R, validR_z0R⟩

theorem mem_qGensA (i : Fin 14) : qGensA[i.val]! ∈ qGensA := by
  rw [getElem!_pos qGensA i.val (by simp [qGensA, phiArr])]
  exact Array.getElem_mem _

theorem gQ_comm_vCert (i : Fin 14) :
    gQ i * d4z = d4z * gQ i ∧ gQ i * x0D = x0D * gQ i := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := Certificates.certificate300207
  simp only [vCommOK, Array.all_eq_true', Bool.and_eq_true, beq_iff_eq] at h
  have h1 := h _ (mem_qGensA i)
  exact ⟨(Gd.eq_iff ((gd_qGens i).mul gd_z0) (gd_z0.mul (gd_qGens i))).1 h1.1,
    (Gd.eq_iff ((gd_qGens i).mul gd_x0) (gd_x0.mul (gd_qGens i))).1 h1.2⟩

theorem Q2_le_centralizer_d4V :
    Q2 ≤ Subgroup.centralizer (d4V : Set D) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  obtain ⟨c0, c1⟩ := gQ_comm_vCert i
  rw [x0D_eq_vB] at c1
  show gQ i ∈ Subgroup.centralizer (d4V : Set D)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [SetLike.mem_coe, mem_d4V_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · simp
  · exact c0.symm
  · exact c1.symm
  · rw [← d4V_rels.1]
    calc (d4z * vB) * gQ i = d4z * (vB * gQ i) := mul_assoc _ _ _
      _ = d4z * (gQ i * vB) := by rw [c1]
      _ = (d4z * gQ i) * vB := (mul_assoc _ _ _).symm
      _ = (gQ i * d4z) * vB := by rw [c0]
      _ = gQ i * (d4z * vB) := mul_assoc _ _ _

theorem r0D_not_comm_vB : ¬ r0D * vB = vB * r0D := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := Certificates.certificate300207
  intro hc
  rw [← x0D_eq_vB] at hc
  simp only [r0NotComm, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact h ((Gd.eq_iff (gd_r0.mul gd_x0) (gd_x0.mul gd_r0)).2 hc)

theorem centralizer_d4V_inf_d4U :
    d4U ⊓ Subgroup.centralizer (d4V : Set D) = Q2 := by
  set L : Subgroup D := d4U ⊓ Subgroup.centralizer (d4V : Set D) with hL
  have hle : Q2 ≤ L := le_inf Q2_le_d4U Q2_le_centralizer_d4V
  have hLU : L ≤ d4U := inf_le_left
  have hfin : Finite d4U := Nat.finite_of_card_ne_zero (by rw [card_d4U']; norm_num)
  have hdvd1 : 2048 ∣ Nat.card L := card_Q2 ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card L ∣ 4096 := card_d4U' ▸ Subgroup.card_dvd_of_le hLU
  obtain ⟨t, ht⟩ := hdvd1
  have ht2 : t ∣ 2 := by
    rw [ht] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2048) (by simpa using hdvd2)
  have hne : Nat.card L ≠ 4096 := by
    intro h4096
    have hLeq : L = d4U := Subgroup.eq_of_le_of_card_ge hLU (by rw [h4096, card_d4U'])
    have hr0 : r0D ∈ L := hLeq ▸ r0D_mem_U
    have hvB : vB ∈ (d4V : Set D) := mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    exact r0D_not_comm_vB ((Subgroup.mem_centralizer_iff.1 hr0.2) vB hvB).symm
  have ht1 : t = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 ht2 with h | h
    · exact h
    · exact absurd (by rw [ht, h]) hne
  have hcard : Nat.card L ≤ Nat.card Q2 := by rw [ht, ht1, card_Q2]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [ht, ht1, card_Q2])).symm

theorem qGens_all_comm {x : Array ℕ} {q : D} (hx : Gd x q) (hc : ∀ q' ∈ Q2, q * q' = q' * q) :
    (qGensA.all fun g => mulR x g == mulR g x) = true := by
  rw [Array.all_eq_true']
  intro g hg
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hg
  have hj14 : j < 14 := by simpa [qGensA, phiArr] using hj
  have gj := gd_qGens ⟨j, hj14⟩
  rw [getElem!_pos qGensA j hj] at gj
  rw [beq_iff_eq]
  exact (Gd.eq_iff (hx.mul gj) (gj.mul hx)).2 (hc _ (gQ_mem _))

theorem centerCheck_mem {T : Array (Array ℕ)} (h : centerCheck T = true) {x : Array ℕ} (hx : x ∈ T)
    (hall : (qGensA.all fun g => mulR x g == mulR g x) = true) :
    x = oneR ∨ x = z0R ∨ x = x0A ∨ x = mulR z0R x0A := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  unfold centerCheck at h
  have h := allLt_spec h hi
  rw [getElem!_pos T i hi] at h
  simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

theorem kcCheck_mem {T : Array (Array ℕ)} (h : kcCheck T = true) {x : Array ℕ} (hx : x ∈ T)
    (hall : (qGensA.all fun g => mulR x g == mulR g x) = true) : x = oneR := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  unfold kcCheck at h
  have h := allLt_spec h hi
  rw [getElem!_pos T i hi] at h
  simpa [hall] using h

theorem center_Q2_le :
    ∀ q ∈ Q2, (∀ q' ∈ Q2, q * q' = q' * q) → q ∈ d4V := by
  obtain ⟨-, -, -, -, -, -, -, -, hc, -⟩ := Certificates.certificate300207
  intro q hq hcomm
  obtain ⟨x, hx, hxq⟩ := tQ_complete hq
  rw [mem_d4V_iff]
  have hvC : d4z * x0D = vC := by rw [x0D_eq_vB]; exact d4V_rels.1
  rcases centerCheck_mem hc hx (qGens_all_comm hxq hcomm) with h | h | h | h
  · exact Or.inl ((Gd.eq_iff hxq gd_one).1 h)
  · exact Or.inr (Or.inl ((Gd.eq_iff hxq gd_z0).1 h))
  · exact Or.inr (Or.inr (Or.inl (by rw [← x0D_eq_vB]; exact (Gd.eq_iff hxq gd_x0).1 h)))
  · exact Or.inr (Or.inr (Or.inr (by rw [← hvC]; exact (Gd.eq_iff hxq (gd_z0.mul gd_x0)).1 h)))

theorem Kc_inf_centralizer_Q2 :
    ∀ k ∈ Kc, (∀ q ∈ Q2, k * q = q * k) → k = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc, -⟩ := Certificates.certificate300207
  intro k hk hcomm
  obtain ⟨x, hx, hxk⟩ := tK_complete hk
  exact (Gd.eq_iff hxk gd_one).1 (kcCheck_mem hc hx (qGens_all_comm hxk hcomm))

end CertQ2

theorem closure_B_gens :
    Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D) = d4B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB, -⟩ := Certificates.certificate300207
  have hle : Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D) ≤ d4B := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [y1D_mem_B, y2D_mem_B, zeD_mem_B, r0D_mem_B]
  have hfin : Finite d4B := Nat.finite_of_card_ne_zero (by rw [card_d4B]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcard : Nat.card (Subgroup.closure ({y1D, y2D, zeD, r0D} : Set D)) = 28672 := by
    refine card_closure_of_tab (gi := bGensInv) (pl := bfsPl bGens) ?_ ?_ hB
    · refine forall_mem_of_getElem fun i hi => ?_
      have hi' : i < 4 := by simpa [bGens] using hi
      interval_cases i
      · exact ⟨y1D, Subgroup.subset_closure (by simp), gd_y1⟩
      · exact ⟨y2D, Subgroup.subset_closure (by simp), gd_y2⟩
      · exact ⟨zeD, Subgroup.subset_closure (by simp), gd_z⟩
      · exact ⟨r0D, Subgroup.subset_closure (by simp), gd_r0⟩
    · intro σ hσ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [bGens], gd_y1.1⟩
      · exact ⟨1, by simp [bGens], gd_y2.1⟩
      · exact ⟨2, by simp [bGens], gd_z.1⟩
      · exact ⟨3, by simp [bGens], gd_r0.1⟩
  rw [card_d4B, hcard]

theorem B_le_N : d4B ≤ d4N := inf_le_right

theorem B_le_H : d4B ≤ d4H := inf_le_left

theorem range_nModel_eq_closure :
    nModel.range = Subgroup.closure ({y1D, y2D, zeD, r0D, s0D} : Set D) := by
  have h := range_pgHom (g := fun i : Fin 5 => d4Word (nWords.getD i.val []))
    (relsHold_spec nWords_lt Certificates.certificate300205.2.2)
  refine h.trans (congrArg Subgroup.closure ?_)
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

theorem range_nModel :
    nModel.range = d4N := by
  rw [range_nModel_eq_closure]
  set R : Subgroup D := Subgroup.closure ({y1D, y2D, zeD, r0D, s0D} : Set D) with hR
  have hBR : d4B ≤ R := by
    rw [← closure_B_gens]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
      Or.inr (Or.inr (Or.inr (Or.inl rfl)))]
  have hRN : R ≤ d4N := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [B_le_N y1D_mem_B, B_le_N y2D_mem_B, B_le_N zeD_mem_B, B_le_N r0D_mem_B, s0D_mem_N]
  have hsR : s0D ∈ R := Subgroup.subset_closure (by simp)
  have hfinN : Finite d4N := Nat.finite_of_card_ne_zero (by rw [card_d4N]; norm_num)
  have hfinR : Finite R := Finite.of_injective _ (Subgroup.inclusion_injective hRN)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBR
  have hdiv : Nat.card R ∣ 86016 := card_d4N ▸ Subgroup.card_dvd_of_le hRN
  rw [hk, card_d4B] at hdiv
  have hk3 : k ∣ 3 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 28672) (by simpa using hdiv)
  rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h1 | h3
  · exfalso
    have hRB : d4B = R := Subgroup.eq_of_le_of_card_ge hBR (by rw [hk, h1, card_d4B])
    exact s0D_not_mem_H (B_le_H (hRB ▸ hsR))
  · refine (Subgroup.eq_of_le_of_card_ge hRN ?_).symm.symm
    rw [card_d4N, hk, h3, card_d4B]

theorem nModel_injective :
    Function.Injective nModel := by
  have hc : Nat.card nModel.range = 86016 := by rw [range_nModel, card_d4N]
  refine pgHom_injective _ card_PG_n_le.1 card_PG_n_le.2 ?_
  rw [← range_pgHom (g := fun i : Fin 5 => d4Word (nWords.getD i.val []))
    (relsHold_spec nWords_lt Certificates.certificate300205.2.2)]
  exact hc.ge

@[expose] noncomputable def cm1D : D := y1D * s0D * (y1D⁻¹ * s0D⁻¹)

@[expose] noncomputable def cm2D : D := y2D * s0D * (y2D⁻¹ * s0D⁻¹)

section CertS

theorem closure_phi_commutators : Subgroup.closure (Set.range (phi cm1D cm2D)) = Q2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hin, hS⟩ := Certificates.certificate300207
  have hz := zeD_pow_seven
  have gd1 : Gd (cmA y1A y1iA) cm1D := (gd_y1.mul gd_s0).mul (gd_y1i.mul gd_s0i)
  have gd2 : Gd (cmA y2A y2A) cm2D := (gd_y2.mul gd_s0).mul (gd_y2i.mul gd_s0i)
  have gd1i : Gd (cmiA y1A y1iA) cm1D⁻¹ := by
    have := (gd_s0.mul gd_y1).mul (gd_s0i.mul gd_y1i)
    rwa [show s0D * y1D * (s0D⁻¹ * y1D⁻¹) = cm1D⁻¹ by simp [cm1D, mul_assoc]] at this
  have gd2i : Gd (cmiA y2A y2A) cm2D⁻¹ := by
    have := (gd_s0.mul gd_y2).mul (gd_s0i.mul gd_y2i)
    rwa [show s0D * y2D * (s0D⁻¹ * y2D⁻¹) = cm2D⁻¹ by simp [cm2D, mul_assoc]] at this
  have hgd : ∀ i : Fin 14, Gd sGensA[i.val]! (phi cm1D cm2D i) := gd_phiArr hz gd1 gd2
  have hgdi : ∀ i : Fin 14, Gd sGensInvA[i.val]! (phi cm1D cm2D i)⁻¹ :=
    gd_phiArr_inv hz gd1i gd2i
  have hsize : sGensA.size = 14 := by simp [sGensA, phiArr]
  have hle : Subgroup.closure (Set.range (phi cm1D cm2D)) ≤ Q2 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    simp only [sInQ2, Array.all_eq_true'] at hin
    have hm := memR_mem (hin sGensA[i.val]! (by
      rw [getElem!_pos sGensA i.val (by omega)]
      exact Array.getElem_mem _))
    obtain ⟨σ, hσ, hg⟩ := tQ_good _ hm
    have := (Gd.eq_iff hg (hgd i)).1 rfl
    exact this ▸ hσ
  have hcard : Nat.card (Subgroup.closure (Set.range (phi cm1D cm2D))) = 2048 := by
    refine card_closure_of_tab (gi := sGensInvA) (pl := bfsPl sGensA) ?_ ?_ hS
    · refine forall_mem_of_getElem fun i hi => ?_
      have hi' : i < 14 := by omega
      rw [getElem!_pos sGensA i hi]
      have := hgd ⟨i, hi'⟩
      rw [getElem!_pos sGensA i hi] at this
      exact ⟨phi cm1D cm2D ⟨i, hi'⟩, Subgroup.subset_closure ⟨⟨i, hi'⟩, rfl⟩, this⟩
    · rintro _ ⟨j, rfl⟩
      exact ⟨j.val, by omega, (hgd j).1⟩
  have hfin : Finite Q2 := Nat.finite_of_card_ne_zero (by rw [card_Q2]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Q2, hcard])

theorem Q2_le_of_normal
    (X : Subgroup D) (_hX : X ≤ d4N) (hn : ∀ n ∈ d4N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hs : s0D ∈ X) : Q2 ≤ X := by
  have hc : ∀ q ∈ d4N, q * s0D * (q⁻¹ * s0D⁻¹) ∈ X := fun q hq => by
    rw [← mul_assoc]
    exact X.mul_mem (hn q hq s0D hs) (X.inv_mem hs)
  have hc1 : cm1D ∈ X := hc y1D (B_le_N y1D_mem_B)
  have hc2 : cm2D ∈ X := hc y2D (B_le_N y2D_mem_B)
  have hzN : ∀ i : ℕ, zeD ^ i ∈ d4N := fun i => pow_mem (B_le_N zeD_mem_B) i
  rw [← closure_phi_commutators]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  by_cases h : i.val < 7
  · rw [phi_lt h]
    exact hn _ (hzN _) _ hc1
  · rw [phi_ge h]
    exact hn _ (hzN _) _ hc2

end CertS

end CFSG.Quasithin.Background.Harris.R1.D4Vert

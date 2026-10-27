module

public import Certificates.Kernel.B433Alt.FixNode

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.YGroups
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelY442 CFSG.KC.YModel.Sem CFSG.KC.Y333
  CFSG.KC.B433Alt CFSG.Certificates.TwDce

theorem words_ok : (∀ c ∈ CFSG.KD.B4AX.jL, wInH (wOfL ([c] ++ dWL ++ [c] ++ dWL.reverse)) = true ∧
      wList (wOfL ([c] ++ dWL ++ [c] ++ dWL.reverse)) = [c] ++ dWL ++ [c] ++ dWL.reverse) ∧
    (wInH (wOfL (dWL ++ dWL)) = true ∧ wList (wOfL (dWL ++ dWL)) = dWL ++ dWL) ∧
    (wInH (wOfL CFSG.KD.B4AX.j3W) = true ∧ wList (wOfL CFSG.KD.B4AX.j3W) = CFSG.KD.B4AX.j3W) ∧
    (wInH (wOfL (dpW CFSG.KD.B4AX.IT)) = true ∧
      wList (wOfL (dpW CFSG.KD.B4AX.IT)) = dpW CFSG.KD.B4AX.IT) ∧
    (wInH (wOfL dWL) = true ∧ wList (wOfL dWL) = dWL) ∧ CFSG.KD.B4AX.jL = tL := by
  decide +kernel

theorem glChk_iff (i : ℕ) (hi : i < 4) : CFSG.KD.B4AX.glChk i = true := gl_ok i hi

section

theorem rho_eq_one_of {l : List ℕ} (hw : wInH (wOfL l) = true) (hl : wList (wOfL l) = l)
    (h : isOne CFSG.KD.B4A.LP (wOfL l) = true) :
    rho432F (evalWord (yGen 4 3 2) l) = 1 := by
  have := isOne_rho hw h
  rwa [wVal, hl] at this

theorem rho_apply_of {l : List ℕ} (hw : wInH (wOfL l) = true) (hl : wList (wOfL l) = l)
    {x : ℕ} (hx : x < 31671) :
    (rho432F (evalWord (yGen 4 3 2) l) ⟨x, hx⟩ : ℕ) = ev1 CFSG.KD.B4A.LP (wOfL l) x := by
  have := ev1_spec tables hw hx
  rwa [wVal, hl] at this

theorem f0_spec (x : Fin 31671) : CFSG.KD.B4AX.F0.testBit x = decide (d0 x = x) := by
  have h := Nat.eq_of_beq_eq_true (glChk_iff 0 (by norm_num))
  change Nat.land (fixedSet 15 (apP CFSG.KD.YMY432F.Nf 15 dWL (idP 15))) allP = CFSG.KD.B4AX.F0 at h
  rw [← h, nland, Nat.testBit_and, testBit_allP x.2, Bool.and_true]
  unfold fixedSet
  rw [shl1, nxor, Nat.testBit_xor, Sch.testBit_ones', decide_eq_true (by omega : (x : ℕ) < 2 ^ 15),
    Bool.true_xor]
  have hrec := Sch.testBit_orRec (fun b => Nat.land (Nat.xor (Nat.shiftRight
    (apP CFSG.KD.YMY432F.Nf 15 dWL (idP 15)) (Nat.mul b (2 ^ 15))) (idPlane (2 ^ 15) b))
    (CFSG.KC.MonsterConv.Perm.ones (2 ^ 15))) x 15
  have hdl : ∀ c ∈ dWL, c < 10 := hub_data.2.2.2.1
  have hb : ∀ b < 15, (Nat.land (Nat.xor (Nat.shiftRight (apP CFSG.KD.YMY432F.Nf 15 dWL (idP 15))
      (Nat.mul b (2 ^ 15))) (idPlane (2 ^ 15) b)) (CFSG.KC.MonsterConv.Perm.ones (2 ^ 15))).testBit x =
      ((d0 x : ℕ).testBit b != (x : ℕ).testBit b) := by
    intro b hb
    rw [nland, nxor, nshr, nmul, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      Sch.testBit_ones', decide_eq_true (by omega : (x : ℕ) < 2 ^ 15), Bool.and_true,
      idPlane_testBit hb, decide_eq_true (by omega : (x : ℕ) < 2 ^ 15), Bool.true_and,
      show b * 2 ^ 15 + (x : ℕ) = 2 ^ 15 * b + x by ring, apP_spec dWL hdl 15 _ b x hb x.2,
      testBit_idP hb (by omega)]
    rfl
  cases hfx : decide (d0 x = x)
  · rw [Bool.not_eq_false']
    rw [decide_eq_false_iff_not] at hfx
    have : ∃ b < 15, (d0 x : ℕ).testBit b ≠ (x : ℕ).testBit b := by
      by_contra hall
      push Not at hall
      exact hfx (Fin.ext (eq_of_bits (k := 15) (by omega) (by omega) hall))
    obtain ⟨b, hb', hne⟩ := this
    exact (hrec.2 ⟨b, hb', by rw [hb b hb']; cases h1 : (d0 x : ℕ).testBit b <;>
      cases h2 : (x : ℕ).testBit b <;> simp_all⟩)
  · rw [decide_eq_true_iff] at hfx
    rw [Bool.not_eq_true']
    by_contra hne
    rw [Bool.not_eq_false] at hne
    obtain ⟨b, hb', h1⟩ := hrec.1 hne
    rw [hb b hb', hfx] at h1
    simp at h1

theorem jL_lt : ∀ c ∈ CFSG.KD.B4AX.jL, c < 10 := by decide

theorem orbJ_mem {b R M : ℕ} (hb : b < 31671)
    (h : orbitOK 15 (CFSG.KD.B4AX.jL.map CFSG.KD.YMY432F.Nf) b R M = true) {p : ℕ}
    (hp : M.testBit p = true) : ∃ hp' : p < 31671, ∃ j ∈ Y442Tw.lsub tL,
      rho432F j ⟨b, hb⟩ = ⟨p, hp'⟩ := by
  obtain ⟨hp', hmem⟩ := orb_mem jL_lt hb h p hp
  rw [lgen_eq, words_ok.2.2.2.2.2] at hmem
  obtain ⟨⟨σ, ⟨j, hj, rfl⟩⟩, hσ⟩ := hmem
  exact ⟨hp', j, hj, hσ⟩

theorem ev_app (u v : List ℕ) : evalWord (yGen 4 3 2) (u ++ v) =
    evalWord (yGen 4 3 2) u * evalWord (yGen 4 3 2) v :=
  CFSG.Certificates.CosetEnumeration.evalWord_append _ u v

theorem rho_sq (c : ℕ) : rho432F (yGen 4 3 2 c) * rho432F (yGen 4 3 2 c) = 1 := by
  rw [← map_mul, yGen_mul_self, map_one]

section

theorem jComm : JComm := by
  intro c hc
  have hcj : c ∈ CFSG.KD.B4AX.jL := by rw [words_ok.2.2.2.2.2]; exact hc
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hcj
  have hlen : CFSG.KD.B4AX.jL.length = 9 := rfl
  have h := lt_ok i (by rw [hlen] at hi; exact hi)
  have hget : CFSG.KD.B4AX.jL.getD i 0 = c := by rw [List.getD_eq_getElem _ _ hi, hci]
  unfold CFSG.KD.B4AX.cChkI at h
  rw [hget] at h
  unfold CFSG.KD.B4AX.cChk at h
  rw [andB_iff] at h
  obtain ⟨hw, hl⟩ := words_ok.1 c hcj
  have h1 := rho_eq_one_of hw hl h.1
  rw [ev_app, ev_app, ev_app, evalWord_rev, evalWord_cons, evalWord_nil, mul_one,
    map_mul, map_mul, map_mul, map_inv, ← dT, ← d0] at h1
  have h2 : rho432F (yGen 4 3 2 c) * d0 * rho432F (yGen 4 3 2 c) = d0 := mul_inv_eq_one.1 h1
  calc rho432F (yGen 4 3 2 c) * d0
      = rho432F (yGen 4 3 2 c) * d0 * (rho432F (yGen 4 3 2 c) * rho432F (yGen 4 3 2 c)) := by
        rw [rho_sq, mul_one]
    _ = d0 * rho432F (yGen 4 3 2 c) := by rw [← mul_assoc, h2]

theorem d0_sq : d0 * d0 = 1 := by
  have h := glChk_iff 3 (by norm_num)
  change isOne CFSG.KD.B4A.LP (wOfL (dWL ++ dWL)) = true at h
  have h1 := rho_eq_one_of words_ok.2.1.1 words_ok.2.1.2 h
  rwa [ev_app, map_mul] at h1

theorem d0_fix0 : d0 0 = 0 := by
  have h := f0_spec 0
  rw [Fin.val_zero, hub_data.2.2.2.2.2.2.2.2.2.2] at h
  exact of_decide_eq_true h.symm

theorem jChk_spec : orbitOK 15 (CFSG.KD.B4AX.jL.map CFSG.KD.YMY432F.Nf) CFSG.KD.B4AX.JO
      CFSG.KD.B4AX.JR CFSG.KD.B4AX.JM = true ∧
    Nat.land (Nat.xor allP CFSG.KD.B4AX.F0) (Nat.xor allP CFSG.KD.B4AX.JM) = 0 ∧
    hubOK CFSG.KD.YMY432F.Nf CFSG.KD.B4AX.JO CFSG.KD.B4AX.JT = true ∧
    isOne CFSG.KD.B4A.LP (wOfL CFSG.KD.B4AX.j3W) = true := by
  have h := glChk_iff 1 (by norm_num)
  change CFSG.KD.B4AX.jChk = true at h
  unfold CFSG.KD.B4AX.jChk at h
  simp only [andB_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1, h.2.2.2⟩

theorem iChk_spec : orbitOK 15 (CFSG.KD.B4AX.jL.map CFSG.KD.YMY432F.Nf) CFSG.KD.B4AX.IW
      CFSG.KD.B4AX.IR CFSG.KD.B4AX.IM = true ∧
    Nat.land (Nat.xor CFSG.KD.B4AX.F0 1) (Nat.xor allP CFSG.KD.B4AX.IM) = 0 ∧
    hubOK CFSG.KD.YMY432F.Nf CFSG.KD.B4AX.IW CFSG.KD.B4AX.IT = true ∧
    ev1 CFSG.KD.B4A.LP (wOfL (dpW CFSG.KD.B4AX.IT)) CFSG.KD.B4AX.IX ≠
      ev1 CFSG.KD.B4A.LP (wOfL dWL) CFSG.KD.B4AX.IX := by
  have h := glChk_iff 2 (by norm_num)
  change CFSG.KD.B4AX.iChk = true at h
  unfold CFSG.KD.B4AX.iChk at h
  simp only [andB_iff] at h
  refine ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1, fun he => ?_⟩
  have h4 := h.2.2.2
  rw [he] at h4
  exact absurd h4 (by decide)

theorem bit_zero_of_land {A B : ℕ} (h : Nat.land A B = 0) {q : ℕ} (hA : A.testBit q = true) :
    B.testBit q = false := by
  have := congrArg (fun x => x.testBit q) h
  simp only [nland, Nat.testBit_and, hA, Bool.true_and, Nat.zero_testBit] at this
  exact this

theorem labFacts : LabFacts where
  comm := jComm
  sq := d0_sq
  fix0 := d0_fix0
  ord3 := by
    intro x hx
    obtain ⟨hJ, hJM, hJO, hJ3⟩ := jChk_spec
    have hdat := hub_data
    have hxF : CFSG.KD.B4AX.F0.testBit x = false := by rw [f0_spec]; exact decide_eq_false hx
    have hA : (Nat.xor allP CFSG.KD.B4AX.F0).testBit x = true := by
      rw [nxor, Nat.testBit_xor, testBit_allP x.2, hxF]; rfl
    have hB := bit_zero_of_land hJM hA
    rw [nxor, Nat.testBit_xor, testBit_allP x.2] at hB
    have hM : CFSG.KD.B4AX.JM.testBit x = true := by
      cases h : CFSG.KD.B4AX.JM.testBit x <;> simp_all
    obtain ⟨hxp, j, hj, hjx⟩ := orbJ_mem hdat.2.2.2.2.2.2.1 hJ hM
    have hlx : lab x = rho432F j * lab ⟨CFSG.KD.B4AX.JO, hdat.2.2.2.2.2.2.1⟩ * (rho432F j)⁻¹ := by
      rw [← lab_conj jComm, hjx]
    have hd : d0 = rho432F j * d0 * (rho432F j)⁻¹ := by rw [J_comm jComm hj]; group
    have h3 : (d0 * lab ⟨CFSG.KD.B4AX.JO, hdat.2.2.2.2.2.2.1⟩) ^ 3 = 1 := by
      have h1 := rho_eq_one_of words_ok.2.2.1.1 words_ok.2.2.1.2 hJ3
      have e : CFSG.KD.B4AX.j3W = (dWL ++ dpW CFSG.KD.B4AX.JT) ++ (dWL ++ dpW CFSG.KD.B4AX.JT) ++
          (dWL ++ dpW CFSG.KD.B4AX.JT) := by
        simp [CFSG.KD.B4AX.j3W]
      rw [e, ev_app, ev_app, ev_app, map_mul, map_mul, map_mul,
        rho_dpW jComm hdat.2.2.2.2.1 hdat.2.2.2.2.2.2.1 hJO, ← dT, ← d0] at h1
      rw [pow_succ, sq]
      exact h1
    rw [hlx]
    nth_rewrite 1 [hd]
    set L := lab ⟨CFSG.KD.B4AX.JO, hdat.2.2.2.2.2.2.1⟩
    have e : rho432F j * d0 * (rho432F j)⁻¹ * (rho432F j * L * (rho432F j)⁻¹) =
        rho432F j * (d0 * L) * (rho432F j)⁻¹ := by group
    rw [e, conj_pow, h3, mul_one, mul_inv_cancel]
  ne0 := by
    intro x hx0 hlx
    have hdat := hub_data
    by_cases hfx : d0 x = x
    · obtain ⟨hI, hIM, hIW, hIX⟩ := iChk_spec
      have hxF : CFSG.KD.B4AX.F0.testBit x = true := by rw [f0_spec]; exact decide_eq_true hfx
      have hA : (Nat.xor CFSG.KD.B4AX.F0 1).testBit x = true := by
        rw [nxor, Nat.testBit_xor, hxF]
        have : (x : ℕ) ≠ 0 := fun h => hx0 (Fin.ext h)
        have h1 : (1 : ℕ).testBit x = false := by
          cases h : (1 : ℕ).testBit x
          · rfl
          · exact absurd (Nat.testBit_one_eq_true_iff_self_eq_zero.1 h) this
        rw [h1]
        rfl
      have hB := bit_zero_of_land hIM hA
      rw [nxor, Nat.testBit_xor, testBit_allP x.2] at hB
      have hM : CFSG.KD.B4AX.IM.testBit x = true := by
        cases h : CFSG.KD.B4AX.IM.testBit x <;> simp_all
      obtain ⟨hxp, j, hj, hjx⟩ := orbJ_mem hdat.2.2.2.2.2.2.2.1 hI hM
      have hlw : lab ⟨CFSG.KD.B4AX.IW, hdat.2.2.2.2.2.2.2.1⟩ = d0 := by
        have e := lab_conj jComm j ⟨CFSG.KD.B4AX.IW, hdat.2.2.2.2.2.2.2.1⟩
        rw [hjx, hlx] at e
        have hc := J_comm jComm hj
        calc lab ⟨CFSG.KD.B4AX.IW, _⟩
            = (rho432F j)⁻¹ * (rho432F j * lab ⟨CFSG.KD.B4AX.IW, _⟩ * (rho432F j)⁻¹) *
                rho432F j := by group
          _ = (rho432F j)⁻¹ * d0 * rho432F j := by rw [← e]
          _ = (rho432F j)⁻¹ * (rho432F j * d0) := by rw [mul_assoc, ← hc]
          _ = d0 := by group
      apply hIX
      rw [← rho_apply_of words_ok.2.2.2.1.1 words_ok.2.2.2.1.2 hdat.2.2.2.2.2.2.2.2.1,
        ← rho_apply_of words_ok.2.2.2.2.1.1 words_ok.2.2.2.2.1.2 hdat.2.2.2.2.2.2.2.2.1,
        rho_dpW jComm hdat.2.2.2.2.2.1 hdat.2.2.2.2.2.2.2.1 hIW, hlw, ← dT, ← d0]
    · apply hfx
      have hs : lab x x = x := by
        rw [lab, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.Perm.inv_eq_iff_eq.2 (eOf_spec x).symm, d0_fix0, eOf_spec]
      rw [← hlx]
      exact hs

end

end

end CertificateChecks.KernelB433

end

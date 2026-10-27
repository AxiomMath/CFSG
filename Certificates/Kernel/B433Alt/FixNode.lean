module

public import Certificates.Kernel.B433Alt.FixSem
public import Certificates.Kernel.B433Alt.FixN
public import Certificates.Kernel.B433Alt.FixI
public import Certificates.Kernel.B433Alt.FixG
public import Certificates.Kernel.B433Alt.Exact
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.YGroups
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelY442 CFSG.KC.YModel.Sem CFSG.KC.Y333
  CFSG.KC.B433Alt

#kc_forall_tree node_ok (fun k => CFSG.KD.B4AX.nodeChk k = true) 22 CFSG.KD.B4AX.node
#kc_forall_tree inv_ok (fun i => CFSG.KD.B4AX.invChk i = true) 111 CFSG.KD.B4AX.inv
#kc_forall_tree rel_ok (fun i => CFSG.KD.B4AX.relChk i = true) 3 CFSG.KD.B4AX.rel
#kc_forall_tree wit_ok (fun i => CFSG.KD.B4AX.witChk i = true) 12 CFSG.KD.B4AX.wit
#kc_forall_tree lt_ok (fun i => CFSG.KD.B4AX.cChkI i = true) 9 CFSG.KD.B4AX.lt
#kc_forall_tree gl_ok (fun i => CFSG.KD.B4AX.glChk i = true) 4 CFSG.KD.B4AX.gl

theorem nj_data : CFSG.KD.B4AX.NJ.length = 22 ∧ CFSG.KD.B4AX.NJ.Nodup ∧
    (∀ k < 22, CFSG.KD.B4AX.NJ.getD k 0 < 64 ∧ liveB (CFSG.KD.B4AX.NJ.getD k 0) = true ∧
      CFSG.KD.B4AT.PA.getD (CFSG.KD.B4AX.NJ.getD k 0) 0 = 0 ∧ CFSG.KD.B4AX.NJ.getD k 0 ≠ 0) := by
  decide +kernel

theorem nj_all : ∀ j < 64, liveB j = true ∧ CFSG.KD.B4AT.PA.getD j 0 = 0 ∧ j ≠ 0 →
    j ∈ CFSG.KD.B4AX.NJ := by
  decide +kernel

theorem sr_data : (∀ g < 5965, isStab (dKind (CFSG.KD.B4A.RD g)) = true →
      dN2 (CFSG.KD.B4A.RD g) ∈ CFSG.KD.B4AX.NJ → g ∈ CFSG.KD.B4AX.SR) ∧
    (∀ i < 111, CFSG.KD.B4AX.SR.getD i 0 < 5965) ∧
    (∀ g ∈ CFSG.KD.B4AX.SR, ∃ i < 111, CFSG.KD.B4AX.SR.getD i 0 = g) := by
  decide +kernel

theorem hub_data : (∀ k < 22, ∀ h ∈ CFSG.KD.B4AX.NH.getD k [], h.1 < 31671 ∧ ∀ c ∈ h.2, c < 10) ∧
    (∀ i < 12, CFSG.KD.B4AX.WW.getD i 0 < 31671 ∧ (∀ c ∈ CFSG.KD.B4AX.WT.getD i [], c < 10) ∧
      CFSG.KD.B4AX.WI.getD i 0 < 12 ∧ CFSG.KD.B4AX.WB.getD i 0 < 31671) ∧
    CFSG.KD.B4AX.WW.length = 12 ∧
    (∀ c ∈ dWL, c < 10) ∧ (∀ c ∈ CFSG.KD.B4AX.JT, c < 10) ∧ (∀ c ∈ CFSG.KD.B4AX.IT, c < 10) ∧
    CFSG.KD.B4AX.JO < 31671 ∧ CFSG.KD.B4AX.IW < 31671 ∧ CFSG.KD.B4AX.IX < 31671 ∧
    CFSG.KD.B4AX.IW ≠ 0 ∧ CFSG.KD.B4AX.F0.testBit 0 = true := by
  decide +kernel

theorem rel_data : CFSG.KD.B4AX.RA.length = 12 ∧ CFSG.KD.B4AX.RA.Nodup ∧
    (∀ a ∈ CFSG.KD.B4AX.RA, a < 31671) ∧ CFSG.KD.B4AX.RS.length = 3 ∧
    (∀ g < 5965, isStab (dKind (CFSG.KD.B4A.RD g)) = true → dN2 (CFSG.KD.B4A.RD g) = 33 →
      ∃ i < 3, (CFSG.KD.B4AX.RS.getD i (0, [])).1 = g) ∧
    (∀ i < 3, (CFSG.KD.B4AX.RS.getD i (0, [])).2.Perm (List.range 12)) ∧
    (∀ i < 3, (CFSG.KD.B4AX.RS.getD i (0, [])).2.length = 12) := by
  decide +kernel

theorem sum_data : 31671 + ∑ k ∈ Finset.range 22,
    CFSG.KD.B4AX.NX.getD k 0 * vN (idxOf (CFSG.KD.B4AX.NJ.getD k 0)) ≤ 75086567571456 := by
  decide +kernel

theorem rec_andB_iff (f : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun i acc => CFSG.KC.B4A.andB acc (f i)) n = true ↔ ∀ i < n, f i = true
  | 0 => by simp
  | n + 1 => by
    change CFSG.KC.B4A.andB (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => CFSG.KC.B4A.andB acc (f i)) n) (f n) = true ↔ _
    rw [andB_iff, rec_andB_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem wList_lt {w : ℕ} (hw : wInH w = true) : ∀ c ∈ wList w, c < 10 := by
  unfold wInH at hw
  rw [andB_iff] at hw
  have h := (rec_andB_iff (fun i => Nat.blt (wAt w i) 10) (wLen w)).1 hw.2
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  exact Nat.blt_eq.mp (h i (List.mem_range.1 hi))

theorem evalWord_rev (w : List ℕ) :
    evalWord (yGen 4 3 2) w.reverse = (evalWord (yGen 4 3 2) w)⁻¹ :=
  evalWord_reverse (yGen_mul_self 4 3 2) w

theorem testBit_ones_sub {n q : ℕ} (hq : q < n) :
    (Nat.sub (Nat.shiftLeft 1 n) 1).testBit q = true := by
  rw [shl1]
  change (2 ^ n - 1).testBit q = true
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hq

theorem testBit_allP {q : ℕ} (hq : q < 31671) : allP.testBit q = true := testBit_ones_sub hq

theorem testBit_sideOf (Y p : ℕ) {q : ℕ} (hq : q < 31671) :
    (sideOf Y p).testBit q = (Y.testBit q != Y.testBit p) := by
  unfold sideOf
  rw [CFSG.KC.YModel.Chain.bitB_eq]
  cases h : Y.testBit p
  · simp
  · change (Nat.xor allP Y).testBit q = _
    rw [CFSG.KC.Benes.nxor, Nat.testBit_xor, testBit_allP hq]
    cases Y.testBit q <;> rfl

section

theorem hubOK_spec {p : ℕ} {τ : List ℕ} (hτ : ∀ c ∈ τ, c < 10) (hp : p < 31671)
    (h : hubOK CFSG.KD.YMY432F.Nf p τ = true) : rho432F (evalWord (yGen 4 3 2) τ) 0 = ⟨p, hp⟩ := by
  have hb := congrArg (fun x => x.testBit p) (Nat.eq_of_beq_eq_true h)
  simp only at hb
  have hτ' : ∀ c ∈ τ.reverse, c < 10 := fun c hc => hτ c (List.mem_reverse.1 hc)
  rw [apP1_spec hτ' 1 ⟨p, hp⟩, shl1, Nat.testBit_two_pow_self, evalWord_rev, map_inv,
    Nat.testBit_one_eq_true_iff_self_eq_zero] at hb
  have h0 : (rho432F (evalWord (yGen 4 3 2) τ))⁻¹ ⟨p, hp⟩ = 0 := Fin.ext hb
  rw [Equiv.Perm.inv_eq_iff_eq] at h0
  exact h0.symm

theorem evalWord_dpW (τ : List ℕ) : evalWord (yGen 4 3 2) (dpW τ) =
    evalWord (yGen 4 3 2) τ * dT * (evalWord (yGen 4 3 2) τ)⁻¹ := by
  rw [dpW, CFSG.Certificates.CosetEnumeration.evalWord_append,
    CFSG.Certificates.CosetEnumeration.evalWord_append, evalWord_rev, dT]

theorem dpW_lt {τ : List ℕ} (hτ : ∀ c ∈ τ, c < 10) : ∀ c ∈ dpW τ, c < 10 := by
  intro c hc
  simp only [dpW, List.mem_append, List.mem_reverse] at hc
  rcases hc with (h | h) | h
  · exact hτ c h
  · exact hub_data.2.2.2.1 c h
  · exact hτ c h

theorem rho_dpW (hcJ : JComm) {p : ℕ} {τ : List ℕ} (hτ : ∀ c ∈ τ, c < 10) (hp : p < 31671)
    (h : hubOK CFSG.KD.YMY432F.Nf p τ = true) :
    rho432F (evalWord (yGen 4 3 2) (dpW τ)) = lab ⟨p, hp⟩ := by
  rw [lab_eq hcJ (hubOK_spec hτ hp h), evalWord_dpW, map_mul, map_mul, map_inv, d0]

theorem hubE_spec (hL : LabFacts) {Y F0 p : ℕ} {τ : List ℕ} (hτ : ∀ c ∈ τ, c < 10) (hp : p < 31671)
    (h : hubOK CFSG.KD.YMY432F.Nf p τ = true)
    (hF0 : ∀ x : Fin 31671, F0.testBit x = decide (d0 x = x)) (ω : Fin 31671)
    (hω : (hubE CFSG.KD.YMY432F.Nf Y F0 p τ).testBit ω = true) :
    lab ⟨p, hp⟩ ω ≠ ω ∧ (Y.testBit (lab ⟨p, hp⟩ ω) = true ↔ Y.testBit p = false) := by
  unfold hubE at hω
  rw [CFSG.KC.Benes.nland, Nat.testBit_and, Bool.and_eq_true, CFSG.KC.Benes.nxor,
    Nat.testBit_xor, testBit_allP ω.2] at hω
  obtain ⟨h1, h2⟩ := hω
  rw [apP1_spec (dpW_lt hτ), rho_dpW hL.comm hτ hp h, testBit_sideOf _ _ (lab _ ω).2] at h1
  have hτ' : ∀ c ∈ τ.reverse, c < 10 := fun c hc => hτ c (List.mem_reverse.1 hc)
  rw [apP1_spec hτ', hF0, evalWord_rev] at h2
  refine ⟨fun he => ?_, ?_⟩
  ·
    apply absurd h2
    rw [Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not, not_not]
    have hl := lab_eq hL.comm (hubOK_spec hτ hp h)
    rw [hl, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at he
    rw [map_inv]
    calc d0 ((rho432F (evalWord (yGen 4 3 2) τ))⁻¹ ω)
        = (rho432F (evalWord (yGen 4 3 2) τ))⁻¹
            (rho432F (evalWord (yGen 4 3 2) τ) (d0 ((rho432F (evalWord (yGen 4 3 2) τ))⁻¹ ω))) := by
          simp
      _ = (rho432F (evalWord (yGen 4 3 2) τ))⁻¹ ω := by rw [he]
  · cases hy : Y.testBit p <;> simp_all

theorem nodeX_spec {Y F0 : ℕ} : ∀ (H : List (ℕ × List ℕ)) (ω : Fin 31671),
    (nodeX CFSG.KD.YMY432F.Nf Y F0 H).testBit ω = false →
      ∃ h ∈ H, (hubE CFSG.KD.YMY432F.Nf Y F0 h.1 h.2).testBit ω = true
  | [], ω, hω => by
    change allP.testBit ω = false at hω
    rw [testBit_allP ω.2] at hω
    exact absurd hω (by decide)
  | h :: H, ω, hω => by
    change (Nat.land (nodeX CFSG.KD.YMY432F.Nf Y F0 H)
      (Nat.xor allP (hubE CFSG.KD.YMY432F.Nf Y F0 h.1 h.2))).testBit ω = false at hω
    rw [CFSG.KC.Benes.nland, Nat.testBit_and, CFSG.KC.Benes.nxor, Nat.testBit_xor,
      testBit_allP ω.2] at hω
    cases h1 : (nodeX CFSG.KD.YMY432F.Nf Y F0 H).testBit ω
    · obtain ⟨h', hm, he⟩ := nodeX_spec H ω h1
      exact ⟨h', List.mem_cons_of_mem _ hm, he⟩
    · rw [h1, Bool.true_and, Bool.true_xor, Bool.not_eq_false'] at hω
      exact ⟨h, List.mem_cons_self, hω⟩

end

end CertificateChecks.KernelB433

end

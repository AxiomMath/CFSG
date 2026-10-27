module

public import Certificates.Kernel.Bounds.HS.Rels
public import Certificates.Kernel.Bounds.HS.Facts
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X1_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X3_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.T_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X1_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X1_W_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X1_C_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X2_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X2_C_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X3_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X3_W_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X3_C_0
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHS

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

noncomputable abbrev S : Subgroup (PresentedGroup P.relatorSet) :=
  Subgroup.closure ((fun j => bval tg (wWord (CFSG.KD.HSKT.selST j)) (wLen (CFSG.KD.HSKT.selST j))) ''
    {j | j < nat_lit 30})

theorem closure_tg : Subgroup.closure (tg '' {g | 2 * g < nat_lit 4}) = ⊤ := by
  rw [← closure_pgen P.relatorSet]
  congr 2
  ext g
  change 2 * g < 4 ↔ g < P.generatorCount
  rw [gens_eq]
  omega

theorem t_index : S.relIndex ⊤ ≠ 0 ∧ S.relIndex ⊤ ≤ 5600 := by
  have h := lceOk_intro (nR := nat_lit 13) (nS := nat_lit 30) CFSG.KD.HSKT.sH1 CFSG.KD.HSKT.sH0
    (by quickRfl) CFSG.KD.HSKT.sH2 CFSG.KD.HSKT.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) Tfacts (by quickRfl) (by quickRfl) Tcover (by quickRfl)
  have s := lceOk_sound h tg (fun r hr => rel_val r hr)
  rw [closure_tg] at s
  exact s

@[expose] noncomputable def gF (k : ℕ) : FreeGroup (Fin 30) :=
  if h : k < 30 then FreeGroup.of ⟨k, h⟩ else 1

@[expose] def relsX : Set (FreeGroup (Fin 30)) :=
  Set.range fun r : Fin 87 => bval gF (wWord (CFSG.KD.HSKM.XRs r)) (wLen (CFSG.KD.HSKM.XRs r))

abbrev XT : Type := PresentedGroup relsX

noncomputable abbrev gX : ℕ → XT := pgen relsX

theorem gX_eq (k : ℕ) : gX k = PresentedGroup.mk relsX (gF k) := by
  simp only [gX, pgen, gF]
  split_ifs <;> simp [PresentedGroup.of]

theorem xrel {r : ℕ} (hr : r < 87) :
    bval gX (wWord (CFSG.KD.HSKM.XRs r)) (wLen (CFSG.KD.HSKM.XRs r)) = 1 := by
  rw [bval_congr gX_eq, ← bval_map]
  exact PresentedGroup.one_of_mem ⟨⟨r, hr⟩, rfl⟩

theorem bval_one {G : Type*} [Group G] (gen : ℕ → G) (j : ℕ) (hj : j < 127) :
    bval gen (wWord (4 + 4096 * (2 * j))) (wLen (4 + 4096 * (2 * j))) = gen j := by
  have h1 : wWord (4 + 4096 * (2 * j)) = 2 * j := by
    change (4 + 4096 * (2 * j)) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : wLen (4 + 4096 * (2 * j)) = 1 := by
    change ((4 + 4096 * (2 * j)) >>> 2) &&& (2 ^ 10 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e1 : 2 * j / 2 ^ (8 * 0) % 256 = 2 * j := by
    rw [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  rw [h1, h2, bval_succ, show bval gen (2 * j / 256) 0 = 1 from rfl, mul_one, wLet_eq, e1]
  unfold letV
  have e2 : ¬ 2 * j = 255 := by omega
  have e3 : 2 * j % 2 = 0 := by omega
  have e4 : 2 * j / 2 = j := by omega
  simp only [e2, e3, e4, ↓reduceIte]

theorem relX {lit : ℕ → ℕ} {n : ℕ} (hn : n ≤ 87) (h : ∀ r < n, lit r = CFSG.KD.HSKM.XRs r) :
    ∀ r < n, bval gX (wWord (lit r)) (wLen (lit r)) = 1 := by
  intro r hr
  rw [h r hr]
  exact xrel (by omega)

theorem image_one {lit : ℕ → ℕ} {n : ℕ} (hn : n < 127) (h : ∀ j < n, lit j = 4 + 4096 * (2 * j)) :
    (fun j => bval gX (wWord (lit j)) (wLen (lit j))) '' {j | j < n} = gX '' {g | 2 * g < 2 * n} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [h j hj, bval_one gX j (by omega)]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [h j (by omega), bval_one gX j (by omega)]⟩

theorem xt_card : Finite XT ∧ Nat.card XT ≤ 12 * (1320 * 1) := by
  have h1 := lceOk_intro (nR := nat_lit 18) (nS := nat_lit 0) CFSG.KD.HSKX1.sH1 CFSG.KD.HSKX1.sH0
    (by quickRfl) CFSG.KD.HSKX1.sH2 CFSG.KD.HSKX1.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.HSKX1.sW0 (by quickRfl) (by quickRfl)
    CFSG.KD.HSKX1.sC0 (by quickRfl)
  have s1 := lceOk_sound h1 gX (relX (by decide) fun r hr => by
    change r < 18 at hr
    interval_cases r <;> exact Nat.eq_of_beq_eq_true (by quickRfl))
  have h2 := lceOk_intro (nR := nat_lit 60) (nS := nat_lit 2) CFSG.KD.HSKX2.sH1 CFSG.KD.HSKX2.sH0
    (by quickRfl) CFSG.KD.HSKX2.sH2 CFSG.KD.HSKX2.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) X2facts (by quickRfl) (by quickRfl)
    CFSG.KD.HSKX2.sC0 (by quickRfl)
  have s2 := lceOk_sound h2 gX (relX (by decide) fun r hr => by
    change r < 60 at hr
    interval_cases r <;> exact Nat.eq_of_beq_eq_true (by quickRfl))
  have h3 := lceOk_intro (nR := nat_lit 87) (nS := nat_lit 3) CFSG.KD.HSKX3.sH1 CFSG.KD.HSKX3.sH0
    (by quickRfl) CFSG.KD.HSKX3.sH2 CFSG.KD.HSKX3.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.HSKX3.sW0 (by quickRfl) (by quickRfl)
    CFSG.KD.HSKX3.sC0 (by quickRfl)
  have s3 := lceOk_sound h3 gX (relX (by decide) fun r hr => by
    change r < 87 at hr
    interval_cases r <;> exact Nat.eq_of_beq_eq_true (by quickRfl))
  have e1 : (fun j => bval gX (wWord (CFSG.KD.HSKX1.selST j)) (wLen (CFSG.KD.HSKX1.selST j))) ''
      {j | j < nat_lit 0} = ∅ :=
    Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun j hj => Nat.not_lt_zero j hj)
  have e2 : (fun j => bval gX (wWord (CFSG.KD.HSKX2.selST j)) (wLen (CFSG.KD.HSKX2.selST j))) ''
      {j | j < nat_lit 2} = gX '' {g | 2 * g < nat_lit 4} :=
    image_one (n := 2) (by norm_num) fun j hj => by
      interval_cases j <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  have e3 : (fun j => bval gX (wWord (CFSG.KD.HSKX3.selST j)) (wLen (CFSG.KD.HSKX3.selST j))) ''
      {j | j < nat_lit 3} = gX '' {g | 2 * g < nat_lit 6} :=
    image_one (n := 3) (by norm_num) fun j hj => by
      interval_cases j <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  have e4 : Subgroup.closure (gX '' {g | 2 * g < nat_lit 60}) = ⊤ := by
    have e : {g : ℕ | 2 * g < nat_lit 60} = {g | g < 30} := by
      ext g
      change 2 * g < 60 ↔ g < 30
      omega
    rw [e]
    exact closure_pgen relsX
  rw [e1, Subgroup.closure_empty, Subgroup.relIndex_bot_left] at s1
  rw [e2] at s2
  rw [e3, e4] at s3
  have m2 : Subgroup.closure (gX '' {g | 2 * g < nat_lit 4}) ≤
      Subgroup.closure (gX '' {g | 2 * g < nat_lit 6}) := by
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, by change 2 * g < 4 at hg; change 2 * g < 6; omega, rfl⟩
  have c2 := KB.card_le_step ⟨m2, s2.1, s2.2⟩ s1
  have c3 := KB.card_le_step ⟨le_top, s3.1, s3.2⟩ c2
  rw [Subgroup.card_top] at c3
  exact ⟨Nat.finite_of_card_ne_zero c3.1, c3.2.trans (by norm_num)⟩

end CertificateChecks.KernelHS

end

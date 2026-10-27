module

public import Certificates.Kernel.ChengHeld.PropsAutR
public import Certificates.Kernel.ChengHeld.PresF
public import CFSG.Certificates.Kernel.ChengHeldAutSound
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelRegular

public section

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model CFSG.KC.ChengHeldS2
open CFSG.KC.ChengHeldP CertificateChecks.KernelChengHeld
open CertificateChecks.KernelChengHeld.S2 (IX0 IX1 IV0 IV1 AU0 AU1)

theorem bind0 : bindW 256 9 CH0.T CH0.PL (IX0 0) (IV0 0) = true := by
  have h := p6138_bind01
  simp only [bAnd_iff] at h
  exact h.1

theorem bind1 : bindW 256 9 CH1.T CH1.PL (IX1 0) (IV1 0) = true := by
  have h := p6138_bind01
  simp only [bAnd_iff] at h
  exact h.2

theorem bound0 : Bound (mkReg 0) 256 9 CH0.T CH0.PL CH0.G (IX0 0) (IV0 0) := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH0.G CH0.GI 7 256 CH0.T CH0.PL
      CH0.POS CH0.SRT CH0.SRI i = true := fun i hi =>
    penumSl_spec k0_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 0 = penumRec 256 9 256 CH0.T CH0.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k0_gens) k0_hd hp).1
  rw [mkReg_eq]
  exact bound_of (regData (α := 0) (by norm_num) chPres_true) (regGens_size 0 (by norm_num)) hE
    (gensOK_of k0_gens) bind0

theorem bound1 : Bound (mkReg 1) 256 9 CH1.T CH1.PL CH1.G (IX1 0) (IV1 0) := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH1.G CH1.GI 7 256 CH1.T CH1.PL
      CH1.POS CH1.SRT CH1.SRI i = true := fun i hi =>
    penumSl_spec k1_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 1 = penumRec 256 9 256 CH1.T CH1.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k1_gens) k1_hd hp).1
  rw [mkReg_eq]
  exact bound_of (regData (α := 1) (by norm_num) chPres_true) (regGens_size 1 (by norm_num)) hE
    (gensOK_of k1_gens) bind1

theorem bound2 : Bound (mkReg 2) 128 8 CH2.T CH2.PL CH2.G (IX2 0) (IV2 0) := by
  have hp : ∀ i < 128, penumPtK 128 8 (mask 8) (128 * 8) false CH2.G CH2.GI 7 128 CH2.T CH2.PL
      CH2.POS CH2.SRT CH2.SRI i = true := fun i hi =>
    penumSl_spec k2_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 2 = penumRec 128 8 128 CH2.T CH2.PL :=
    (penumK_left_sound (cap := 128) (by decide) (gensOK_of k2_gens) k2_hd hp).1
  rw [mkReg_eq]
  exact bound_of (regData (α := 2) (by norm_num) chPres_true) (regGens_size 2 (by norm_num)) hE
    (gensOK_of k2_gens) p6138_bind

theorem mlt_of {α n w : ℕ} {T PL G : ℕ → ℕ} {IXP IVP : ℕ} (hα : α ≤ 2)
    (hB : Bound (mkReg α) n w T PL G IXP IVP) :
    ∀ x y, x < n → y < n → mW n w T IXP x y < n := by
  intro x y hx hy
  have hd := regData hα chPres_true
  rw [mkReg_eq] at hB
  have h := hd.rep.m_lt_of_lt (a := x) (b := y) (by rw [hB.N_eq]; exact hx)
    (by rw [hB.N_eq]; exact hy)
  rw [hB.m_eq, hB.N_eq] at h
  exact h

theorem aut0 : autOK 0 = true := by
  have r := p6138_rec0
  have l := p6138_lt
  have h := p6138_hom0
  have i := p6138_invo
  have c := p6138_cl0
  simp only [bAnd_iff] at r l h i
  simp only [Bool.and_eq_true] at c
  refine autOK_bound (A := AU0) bound0 (by norm_num) (mlt_of (by norm_num) bound0)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (by simp only [Bool.and_eq_true]; exact c.1.1) p6138_aut0 <;> interval_cases k
  exacts [r.1, r.2.1, r.2.2, l.1.1.1, l.1.1.2.1, l.1.1.2.2, h.1, h.2.1, h.2.2.1, i.1.1, i.1.2.1,
    i.1.2.2]

theorem aut1 : autOK 1 = true := by
  have r := p6138_rec1
  have l := p6138_lt
  have h := p6138_hom1
  have i := p6138_invo
  have c := p6138_cl1
  simp only [bAnd_iff] at r l h i
  simp only [Bool.and_eq_true] at c
  refine autOK_bound (A := AU1) bound1 (by norm_num) (mlt_of (by norm_num) bound1)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (by simp only [Bool.and_eq_true]; exact c.1.1) p6138_aut1 <;> interval_cases k
  exacts [r.1, r.2.1, r.2.2, l.2.1.1.1, l.2.1.1.2.1, l.2.1.1.2.2, h.1, h.2.1, h.2.2.1, i.2.1.1,
    i.2.1.2.1, i.2.1.2.2]

theorem aut2 : autOK 2 = true := by
  have r := p6138_rec2
  have l := p6138_lt
  have h := p6138_hom2
  have i := p6138_invo
  have c := p6138_cl2
  simp only [bAnd_iff] at r l h i
  simp only [Bool.and_eq_true] at c
  refine autOK_bound (A := AU2) bound2 (by norm_num) (mlt_of (by norm_num) bound2)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (by simp only [Bool.and_eq_true]; exact c.1) p6138_aut2 <;> interval_cases k
  exacts [r.1, r.2.1, r.2.2, l.2.2.1.1, l.2.2.1.2.1, l.2.2.1.2.2, h.1, h.2.1, h.2.2.1, i.2.2.1,
    i.2.2.2.1, i.2.2.2.2]

theorem gAut0 : gAutOK 0 = true := by
  have r := p6138_recg
  have l := p6138_lt
  have h := p6138_hom0
  have o := p6138_g
  have c := p6138_cl0
  simp only [bAnd_iff, Bool.and_eq_true] at r l h o c
  exact gAutOK_bound bound0 (by norm_num) (mlt_of (by norm_num) bound0)
    bind0 r.1 l.1.2 h.2.2.2 o.1
    (by simp only [Bool.and_eq_true]; exact ⟨c.1.2, c.1.1.1.2⟩) (fun _ => c.2) p6138_orb0
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)) p6138_g0

theorem gAut1 : gAutOK 1 = true := by
  have r := p6138_recg
  have l := p6138_lt
  have h := p6138_hom1
  have o := p6138_g
  have c := p6138_cl1
  simp only [bAnd_iff, Bool.and_eq_true] at r l h o c
  exact gAutOK_bound bound1 (by norm_num) (mlt_of (by norm_num) bound1)
    bind1 r.2.1 l.2.1.2 h.2.2.2 o.2.1
    (by simp only [Bool.and_eq_true]; exact ⟨c.1.2, c.1.1.1.2⟩) (fun _ => c.2) p6138_orb1
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)) p6138_g1

theorem gAut2 : gAutOK 2 = true := by
  have r := p6138_recg
  have l := p6138_lt
  have h := p6138_hom2
  have o := p6138_g
  have c := p6138_cl2
  have ob := p6138_orb2
  simp only [bAnd_iff, Bool.and_eq_true] at r l h o c ob
  exact gAutOK_bound bound2 (by norm_num) (mlt_of (by norm_num) bound2) p6138_bind r.2.2 l.2.2.2
    h.2.2.2 o.2.2 (by simp only [Bool.and_eq_true]; exact ⟨c.2, c.1.1.2⟩)
    (fun h => absurd rfl h) ob.1.1 (fun _ => ob.1.2) (fun _ => ob.2) p6138_g2

end CertificateChecks.KernelChengHeld.P

end

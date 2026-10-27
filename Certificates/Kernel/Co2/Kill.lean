module

public import Certificates.Kernel.Co2.Pair
public import Certificates.Kernel.Co2.Model
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.M
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.C_H_0
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.C_W_0
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.C_L
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Co2K CFSG.Certificates CFSG.Certificates.LCE
  CFSG.Certificates.Co2Kill

noncomputable abbrev piG (k : ℕ) : PresentedGroup P.relatorSet :=
  bval tg (wWord (Co2K.gen (k + 1))) (wLen (Co2K.gen (k + 1)))

theorem lift_gF {G : Type*} [Group G] (f : Fin 5 → G) (k : ℕ) :
    FreeGroup.lift f (gF k) = if h : k < 5 then f ⟨k, h⟩ else 1 := by
  unfold gF
  split_ifs <;> simp [FreeGroup.lift_apply_of]

theorem piG_ge {k : ℕ} (h : ¬ k < 5) : piG k = 1 := by
  unfold piG
  rw [gen_ge (by omega)]
  rfl

noncomputable def piX : XT →* PresentedGroup P.relatorSet :=
  PresentedGroup.toGroup (f := fun t : Fin 5 => piG t) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := piG) fun k => by
      rw [lift_gF]
      split_ifs with h
      · rfl
      · exact (piG_ge h).symm]
    exact pi_rel r hr)

theorem piX_gX {k : ℕ} (hk : k < 5) : piX (gX k) = piG k := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

theorem fi_inv : ∀ t : Fin 5, invol7 (CFSG.KD.Co2KM.FIs t) = true := by
  intro t
  fin_cases t
  exacts [CFSG.KD.Co2KM.inv0, CFSG.KD.Co2KM.inv1, CFSG.KD.Co2KM.inv2, CFSG.KD.Co2KM.inv3,
    CFSG.KD.Co2KM.inv4]

@[expose] noncomputable def uG (t : Fin 5) : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ :=
  unit7 (CFSG.KD.Co2KM.FIs t) (fi_inv t)

theorem uG_inv (t : Fin 5) : (uG t)⁻¹ = uG t := Units.ext rfl

theorem uG_val (t : Fin 5) : ((uG t : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
    dec7 (CFSG.KD.Co2KM.FIs t) := rfl

theorem lettersBelow_spec {W n b : ℕ} (h : HO.lettersBelow W n b = true) : ∀ q < n, wLet W q < b := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    have h' : andB (HO.lettersBelow W n b) (Nat.blt (wLet W n) b) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact ih h1 q hq
    · simpa using h2

theorem psi_rel {r : ℕ} (hr : r < 23) :
    bval (fun k => if h : k < 5 then uG ⟨k, h⟩ else 1) (wWord (CFSG.KD.Co2KM.XRs r))
      (wLen (CFSG.KD.Co2KM.XRs r)) = 1 := by
  have hlet : ∀ q < wLen (CFSG.KD.Co2KM.XRs r), wLet (wWord (CFSG.KD.Co2KM.XRs r)) q < 10 := by
    apply lettersBelow_spec
    interval_cases r <;> quickRfl
  have hhom : Nat.beq (evalE CFSG.KD.Co2KM.FIs (CFSG.KD.Co2KM.XRs r)) ONE7 = true := by
    interval_cases r
    exacts [CFSG.KD.Co2KM.hom0, CFSG.KD.Co2KM.hom1, CFSG.KD.Co2KM.hom2, CFSG.KD.Co2KM.hom3,
      CFSG.KD.Co2KM.hom4, CFSG.KD.Co2KM.hom5, CFSG.KD.Co2KM.hom6, CFSG.KD.Co2KM.hom7,
      CFSG.KD.Co2KM.hom8, CFSG.KD.Co2KM.hom9, CFSG.KD.Co2KM.hom10, CFSG.KD.Co2KM.hom11,
      CFSG.KD.Co2KM.hom12, CFSG.KD.Co2KM.hom13, CFSG.KD.Co2KM.hom14, CFSG.KD.Co2KM.hom15,
      CFSG.KD.Co2KM.hom16, CFSG.KD.Co2KM.hom17, CFSG.KD.Co2KM.hom18, CFSG.KD.Co2KM.hom19,
      CFSG.KD.Co2KM.hom20, CFSG.KD.Co2KM.hom21, CFSG.KD.Co2KM.hom22]
  have hidx : ∀ q < wLen (CFSG.KD.Co2KM.XRs r),
      Nat.shiftRight (byte (wWord (CFSG.KD.Co2KM.XRs r)) q) 1 = wLet (wWord (CFSG.KD.Co2KM.XRs r)) q / 2 :=
    fun q _ => Nat.shiftRight_eq_div_pow _ 1
  have hwf : ∀ q < wLen (CFSG.KD.Co2KM.XRs r),
      wf7 (CFSG.KD.Co2KM.FIs (Nat.shiftRight (byte (wWord (CFSG.KD.Co2KM.XRs r)) q) 1)) = true := by
    intro q hq
    rw [hidx q hq]
    have := hlet q hq
    exact (KB.andB_true (fi_inv ⟨_, by omega⟩)).1
  obtain ⟨-, hd⟩ := evalE_dec CFSG.KD.Co2KM.FIs (CFSG.KD.Co2KM.XRs r) hwf
  rw [Nat.eq_of_beq_eq_true hhom, dec7_one] at hd
  apply Units.ext
  rw [Units.val_one, hd.trans rfl]
  unfold bval
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hq' := List.mem_range.mp hq
  have hc := hlet q hq'
  simp only [Function.comp_apply, Units.coeHom_apply]
  rw [hidx q hq']
  unfold letV
  have h255 : ¬ wLet (wWord (CFSG.KD.Co2KM.XRs r)) q = 255 := by omega
  have h5 : wLet (wWord (CFSG.KD.Co2KM.XRs r)) q / 2 < 5 := by omega
  simp only [h255, h5, ↓reduceIte, dite_true]
  split_ifs
  · exact uG_val _
  · rw [uG_inv]
    exact uG_val _

noncomputable def psiX : XT →* (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ :=
  PresentedGroup.toGroup (f := uG) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map]
    rw [bval_congr (gen' := fun k => if h : k < 5 then uG ⟨k, h⟩ else 1) fun k => lift_gF uG k]
    exact psi_rel hr)

theorem psiX_gX {k : ℕ} (hk : k < 5) : psiX (gX k) = uG ⟨k, hk⟩ := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

theorem cone_cycle : ∃ ν : XT, piX ν = 1 ∧
    ((psiX ν : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) = dec7 NEG7 := by
  have hC := coneOk_intro (nf := nat_lit 1170) CFSG.KD.Co2KC.sH0 CFSG.KD.Co2KC.sH1 (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.Co2KC.sH6
    (by quickRfl) CFSG.KD.Co2KC.sW0 CFSG.KD.Co2KC.sL0
  refine lab_sound tg piX psiX hC (fun r => rel_all r) ?_ rfl (by decide) CFSG.KD.Co2KC.sY0
  intro j hj
  change j < 4 at hj
  have key : ∀ (t : Fin 5), Nat.beq (lX (CFSG.KD.Co2KC.LETs j)) (CFSG.KD.Co2KM.FIs t) = true →
      Nat.beq (CFSG.KC.Co2K.subH j) (Co2K.gen (t + 1)) = true →
      wf7 (lX (CFSG.KD.Co2KC.LETs j)) = true ∧ ∃ x : XT,
        piX x = bval tg (wWord (CFSG.KD.Co2KC.selST j)) (wLen (CFSG.KD.Co2KC.selST j)) ∧
        ((psiX x : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 (lX (CFSG.KD.Co2KC.LETs j)) := by
    intro t h1 h2
    rw [Nat.eq_of_beq_eq_true h1]
    refine ⟨(KB.andB_true (fi_inv t)).1, gX t, ?_, ?_⟩
    · rw [piX_gX t.isLt]
      change _ = bval tg (wWord (CFSG.KC.Co2K.subH j)) (wLen (CFSG.KC.Co2K.subH j))
      rw [Nat.eq_of_beq_eq_true h2]
    · rw [psiX_gX t.isLt]
      rfl
  interval_cases j
  · exact key 0 (by quickRfl) (by quickRfl)
  · exact key 1 (by quickRfl) (by quickRfl)
  · exact key 2 (by quickRfl) (by quickRfl)
  · exact key 4 (by quickRfl) (by quickRfl)

theorem co2_bound : Finite (PresentedGroup P.relatorSet) ∧
    Nat.card (PresentedGroup P.relatorSet) ≤ 42305421312000 := by
  obtain ⟨ν, hν1, hν2⟩ := cone_cycle
  obtain ⟨hfin, hcard⟩ := xt_card
  have hne : ν ≠ 1 := by
    rintro rfl
    rw [map_one, Units.val_one, ← dec7_one] at hν2
    have := dec7_inj wf7_one wf7_neg hν2
    have hz := CFSG.KD.Co2KC.sZ
    rw [← this] at hz
    simp [notB] at hz
  have hker : piX.ker ≠ ⊥ := by
    intro h
    have hm : ν ∈ piX.ker := MonoidHom.mem_ker.mpr hν1
    rw [h] at hm
    exact hne (Subgroup.mem_bot.mp hm)
  have hk2 : 1 < Nat.card piX.ker := (Subgroup.one_lt_card_iff_ne_bot (H := piX.ker)).mpr hker
  have hmul : Nat.card XT = Nat.card piX.range * Nat.card piX.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup piX.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange piX).toEquiv]
  have hr : Nat.card piX.range ≤ 908328960 := by
    have : Nat.card piX.range * 2 ≤ 1024 * (5280 * 336) :=
      (Nat.mul_le_mul_left _ hk2).trans (hmul ▸ hcard)
    omega
  have hH4 : H4 ≤ piX.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    change j < 4 at hj
    have key : ∀ t : Fin 5, Nat.beq (CFSG.KC.Co2K.subH j) (Co2K.gen (t + 1)) = true →
        bval tg (wWord (CFSG.KD.Co2KP4.selST j)) (wLen (CFSG.KD.Co2KP4.selST j)) ∈ piX.range := by
      intro t h
      refine ⟨gX t, ?_⟩
      rw [piX_gX t.isLt]
      change _ = bval tg (wWord (CFSG.KC.Co2K.subH j)) (wLen (CFSG.KC.Co2K.subH j))
      rw [Nat.eq_of_beq_eq_true h]
    interval_cases j
    · exact key 0 (by quickRfl)
    · exact key 1 (by quickRfl)
    · exact key 2 (by quickRfl)
    · exact key 4 (by quickRfl)
  have hfr : Finite piX.range := Finite.of_surjective _ piX.rangeRestrict_surjective
  have hf4 : Finite H4 := Finite.of_injective _ (Subgroup.inclusion_injective hH4)
  have c4 : Nat.card H4 ≠ 0 ∧ Nat.card H4 ≤ 908328960 :=
    ⟨Nat.card_pos.ne', (Subgroup.card_le_of_le hH4).trans hr⟩
  have c := KB.card_le_step ⟨le_top, p4_index.1, p4_index.2⟩ c4
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelCo2

end

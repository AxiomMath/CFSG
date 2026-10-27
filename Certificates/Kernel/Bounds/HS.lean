module

public import Certificates.Kernel.Bounds.HS.Chain
public import Certificates.Kernel.Bounds.HS.Pair
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.C_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.C_L
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHS

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

theorem lift_gF {G : Type*} [Group G] (f : Fin 30 → G) (k : ℕ) :
    FreeGroup.lift f (gF k) = if h : k < 30 then f ⟨k, h⟩ else 1 := by
  unfold gF
  split_ifs <;> simp [FreeGroup.lift_apply_of]

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

theorem bval_congr_lt {G : Type*} [Group G] {f g : ℕ → G} {N W n : ℕ}
    (hW : ∀ q < n, wLet W q < 2 * N) (hfg : ∀ k < N, f k = g k) :
    bval f W n = bval g W n := by
  unfold bval
  congr 1
  apply List.map_congr_left
  intro q hq
  have hl := hW q (List.mem_range.mp hq)
  unfold letV
  rw [hfg _ (by omega)]

theorem xr_letters {r : ℕ} (hr : r < 87) :
    ∀ q < wLen (CFSG.KD.HSKM.XRs r), wLet (wWord (CFSG.KD.HSKM.XRs r)) q < 2 * 30 := by
  apply lettersBelow_spec
  interval_cases r <;> quickRfl

noncomputable abbrev piG (k : ℕ) : PresentedGroup P.relatorSet :=
  bval tg (wWord (HSK.gen (k + 1))) (wLen (HSK.gen (k + 1)))

noncomputable def piX : XT →* PresentedGroup P.relatorSet :=
  PresentedGroup.toGroup (f := fun t : Fin 30 => piG t) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map, bval_congr_lt (g := piG) (xr_letters hr) (fun k hk => by
      simp [lift_gF, hk])]
    exact pi_rel r hr)

theorem piX_gX {k : ℕ} (hk : k < 30) : piX (gX k) = piG k := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

abbrev one2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem bval_one2 {W n : ℕ} (hW : ∀ q < n, wLet W q < 255) (hn : n % 2 = 0) :
    bval (fun _ => one2) W n = 1 := by
  have hl : ∀ i ∈ List.range n, letV (fun _ => one2) (wLet W i) = one2 := by
    intro i hi
    have h255 : wLet W i ≠ 255 := by
      have := hW i (List.mem_range.mp hi)
      omega
    unfold letV
    simp only [h255, ↓reduceIte]
    split_ifs
    · rfl
    · change one2⁻¹ = one2
      decide
  unfold bval
  rw [List.map_congr_left hl, List.map_const', List.length_range, List.prod_replicate,
    ← Nat.div_add_mod n 2, hn, Nat.add_zero, pow_mul]
  have h2 : one2 ^ 2 = 1 := by decide
  rw [h2, one_pow]

theorem xr_even {r : ℕ} (hr : r < 87) : wLen (CFSG.KD.HSKM.XRs r) % 2 = 0 := by
  have h : Nat.beq (Nat.land (wLen (CFSG.KD.HSKM.XRs r)) 1) 0 = true := by
    interval_cases r <;> quickRfl
  rw [← Nat.and_one_is_mod]
  exact Nat.eq_of_beq_eq_true h

noncomputable def psiX : XT →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ : Fin 30 => one2) (by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    rw [bval_map, bval_congr_lt (g := fun _ => one2) (xr_letters hr) (fun k hk => by
      simp [lift_gF, hk])]
    exact bval_one2 (fun q hq => by have := xr_letters hr q hq; omega) (xr_even hr))

theorem psiX_gX {k : ℕ} (hk : k < 30) : psiX (gX k) = one2 := by
  rw [show gX k = PresentedGroup.of ⟨k, hk⟩ from pgen_lt relsX hk]
  exact PresentedGroup.toGroup.of _

theorem subS_gen : ∀ j < 30, ∃ t : Fin 30, Nat.beq (HSK.subS j) (HSK.gen (t.val + 1)) = true := by
  intro j hj
  interval_cases j
  exacts [⟨3, by quickRfl⟩, ⟨0, by quickRfl⟩, ⟨4, by quickRfl⟩, ⟨5, by quickRfl⟩, ⟨6, by quickRfl⟩,
    ⟨1, by quickRfl⟩, ⟨7, by quickRfl⟩, ⟨8, by quickRfl⟩, ⟨9, by quickRfl⟩, ⟨2, by quickRfl⟩,
    ⟨10, by quickRfl⟩, ⟨11, by quickRfl⟩, ⟨12, by quickRfl⟩, ⟨13, by quickRfl⟩, ⟨14, by quickRfl⟩,
    ⟨15, by quickRfl⟩, ⟨16, by quickRfl⟩, ⟨17, by quickRfl⟩, ⟨18, by quickRfl⟩, ⟨19, by quickRfl⟩,
    ⟨20, by quickRfl⟩, ⟨21, by quickRfl⟩, ⟨22, by quickRfl⟩, ⟨23, by quickRfl⟩, ⟨24, by quickRfl⟩,
    ⟨25, by quickRfl⟩, ⟨26, by quickRfl⟩, ⟨27, by quickRfl⟩, ⟨28, by quickRfl⟩, ⟨29, by quickRfl⟩]

theorem subS_mem : ∀ j < 30, ∃ t : Fin 30,
    piX (gX t) = bval tg (wWord (HSK.subS j)) (wLen (HSK.subS j)) ∧ psiX (gX t) = one2 := by
  intro j hj
  obtain ⟨t, ht⟩ := subS_gen j hj
  refine ⟨t, ?_, psiX_gX t.isLt⟩
  rw [piX_gX t.isLt, Nat.eq_of_beq_eq_true ht]

theorem cone_cycle : ∃ ν : XT, piX ν = 1 ∧ psiX ν = Multiplicative.ofAdd ((1 : ℕ) : ZMod 2) := by
  have hC := coneOk_intro (nf := nat_lit 3757) CFSG.KD.HSKC.sH0 CFSG.KD.HSKC.sH1 (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.HSKC.sH6
    (by quickRfl) Cfacts Clab
  refine HSKill.lab_sound tg piX psiX hC (fun r => rel_all r) ?_ rfl (by decide) (by decide)
    CFSG.KD.HSKC.sY0
  intro j hj
  change j < 30 at hj
  obtain ⟨t, h1, h2⟩ := subS_mem j hj
  exact ⟨Nat.one_lt_two, gX t, h1, by rw [h2]; rfl⟩

theorem hs_bound : Finite (PresentedGroup P.relatorSet) ∧
    Nat.card (PresentedGroup P.relatorSet) ≤ 44352000 := by
  obtain ⟨ν, hν1, hν2⟩ := cone_cycle
  obtain ⟨hfin, hcard⟩ := xt_card
  have hne : ν ≠ 1 := by
    rintro rfl
    rw [map_one] at hν2
    exact absurd hν2 (by decide)
  have hker : piX.ker ≠ ⊥ := by
    intro h
    have hm : ν ∈ piX.ker := MonoidHom.mem_ker.mpr hν1
    rw [h] at hm
    exact hne (Subgroup.mem_bot.mp hm)
  have hk2 : 1 < Nat.card piX.ker := (Subgroup.one_lt_card_iff_ne_bot (H := piX.ker)).mpr hker
  have hmul : Nat.card XT = Nat.card piX.range * Nat.card piX.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup piX.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange piX).toEquiv]
  have hr : Nat.card piX.range ≤ 7920 := by
    have : Nat.card piX.range * 2 ≤ 12 * (1320 * 1) :=
      (Nat.mul_le_mul_left _ hk2).trans (hmul ▸ hcard)
    omega
  have hS : S ≤ piX.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    change j < 30 at hj
    obtain ⟨t, h1, -⟩ := subS_mem j hj
    exact ⟨gX t, h1⟩
  have hfr : Finite piX.range := Finite.of_surjective _ piX.rangeRestrict_surjective
  have hfS : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hS)
  have cS : Nat.card S ≠ 0 ∧ Nat.card S ≤ 7920 :=
    ⟨Nat.card_pos.ne', (Subgroup.card_le_of_le hS).trans hr⟩
  have c := KB.card_le_step ⟨le_top, t_index.1, t_index.2⟩ cS
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelHS

end

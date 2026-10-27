module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5

public section

namespace CFSG.Quasithin.A38c8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem l4_block_model {B' : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))} {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 5) (hBQ : B' ≤ flagStabilizer 5 (ZMod 2) I)
    (hperf : ⁅B', B'⁆ = B')
    (hord : Nat.card (↥B' ⧸ CFSG.pCore 2 ↥B') = 20160) :
    I = ∅ ∨ ((I = {1} ∨ I = {4}) ∧
      ∀ b₀ ∈ flagStabilizer 5 (ZMod 2) I, (∀ x ∈ B', b₀ * x * b₀⁻¹ ∈ B') →
        ∃ b ∈ B', ∀ x ∈ B', ∃ hz : (b₀ * x * b₀⁻¹)⁻¹ * (b * x * b⁻¹) ∈ B',
          (⟨(b₀ * x * b₀⁻¹)⁻¹ * (b * x * b⁻¹), hz⟩ : ↥B') ∈ CFSG.pCore 2 ↥B') := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hne : B' ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (↥(⊥ : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))) ⧸
        CFSG.pCore 2 ↥(⊥ : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2)))) ≤
        Nat.card ↥(⊥ : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))) :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
    rw [Subgroup.card_bot, hord] at h1
    omega
  have hle : B' ≤ perfectCore (flagStabilizer 5 (ZMod 2) I) :=
    le_perfectCore_of_perfect hBQ hperf
  rcases exists_big_or_small (n := 5) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    apply hne
    have h0 := perfectCore_eq_bot_of_small hK (by norm_num) hsmall
    rw [h0] at hle
    exact le_bot_iff.1 hle
  · set f : ↥B' →* SpecialLinearGroup (Fin m) (ZMod 2) :=
      (bigBlockHom (K := ZMod 2) I a m h ha hb).comp (Subgroup.inclusion hle) with hf
    have hker : IsPGroup 2 f.ker := by
      refine isPGroup_ker_of_unitriangular (K := ZMod 2) (by norm_num) f fun x hx => ?_
      exact unitriangular_of_bigBlockHom hK (by norm_num) h hm3 ha hb hno
        (Subgroup.inclusion hle x) hx
    have hkerle : f.ker ≤ CFSG.pCore 2 ↥B' := le_sSup ⟨inferInstance, hker⟩
    have hcard1 : Nat.card ↥B' = Nat.card (↥B' ⧸ CFSG.pCore 2 ↥B') * Nat.card (CFSG.pCore 2 ↥B') :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B')
    have hcard2 : Nat.card f.ker * Nat.card f.range = Nat.card ↥B' :=
      Subgroup.card_ker_mul_card_range f
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hkerle
    have hrange : Nat.card f.range = 20160 * c := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card f.ker)
      rw [hcard2, hcard1, hord, hc]
      ring
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exfalso
        have : 0 < Nat.card f.range := Nat.card_pos
        omega
      · exact h0
    have hle2 : Nat.card f.range ≤ Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) :=
      Subgroup.card_le_card_group f.range
    have hm5 : m ≤ 5 := by omega
    have hcardSL : Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) =
        Nat.card (ZMod 2) ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (Nat.card (ZMod 2) ^ j - 1) :=
      card_SL_eq (by omega)
    rw [Nat.card_zmod] at hcardSL
    have hm : m = 4 ∨ m = 5 := by
      interval_cases m
      · exfalso
        rw [hrange, hcardSL] at hle2
        have h168 : (2 : ℕ) ^ (3 * (3 - 1) / 2) * ∏ j ∈ Finset.Icc 2 3, ((2 : ℕ) ^ j - 1) = 168 := by
          decide
        rw [h168] at hle2
        omega
      · left; rfl
      · right; rfl
    rcases hm with rfl | rfl
    ·
      right
      have h20160 : Nat.card (SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
        rw [hcardSL]
        decide
      have hc1 : c = 1 := by omega
      have hrt : f.range = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        omega
      refine ⟨?_, ?_⟩
      · have ha' : a = 0 ∨ a = 1 := by omega
        rcases ha' with rfl | rfl
        · have h4 : 4 ∈ I := by
            rcases hb with hb | hb
            · omega
            · exact hb
          right
          ext i
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hi
            have := hno i hi
            have := hI i hi
            omega
          · rintro rfl
            exact h4
        · have h1 : 1 ∈ I := by
            rcases ha with ha | ha
            · omega
            · exact ha
          left
          ext i
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hi
            have := hno i hi
            have := hI i hi
            omega
          · rintro rfl
            exact h1
      · intro b₀ hb₀ hn
        set M := blkMon (flagStabilizer 5 (ZMod 2) I) a 4 h (blockLeft_of_cut 4 ha)
          (blockRight_of_cut hb) with hM
        have hfM : ∀ y : ↥B', ((f y : SpecialLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) = M ⟨y.1, hBQ y.2⟩ := fun y => rfl
        have hdet : (M ⟨b₀, hb₀⟩).det = 1 := by
          have h1 : M ⟨b₀, hb₀⟩ * M (⟨b₀, hb₀⟩⁻¹) = 1 := by
            rw [← map_mul, mul_inv_cancel, map_one]
          have h2 : (M ⟨b₀, hb₀⟩).det * (M (⟨b₀, hb₀⟩⁻¹)).det = 1 := by
            rw [← Matrix.det_mul, h1, Matrix.det_one]
          rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (M ⟨b₀, hb₀⟩).det with h0 | h0
          · rw [h0, zero_mul] at h2
            exact absurd h2 zero_ne_one
          · exact h0
        obtain ⟨y, hy⟩ : ∃ y : ↥B', M ⟨y.1, hBQ y.2⟩ = M ⟨b₀, hb₀⟩ := by
          let u : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨M ⟨b₀, hb₀⟩, hdet⟩
          have hmem : u ∈ f.range := by
            rw [hrt]
            exact Subgroup.mem_top u
          obtain ⟨y, hy⟩ := hmem
          exact ⟨y, (hfM y).symm.trans (congrArg Subtype.val hy)⟩
        refine ⟨y.1, y.2, fun x hx => ?_⟩
        have hxQ := hBQ hx
        have hz : (b₀ * x * b₀⁻¹)⁻¹ * (y.1 * x * y.1⁻¹) ∈ B' :=
          B'.mul_mem (B'.inv_mem (hn x hx)) (B'.mul_mem (B'.mul_mem y.2 hx) (B'.inv_mem y.2))
        refine ⟨hz, hkerle ?_⟩
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        rw [hfM]
        have hΦ : M.toHomUnits ⟨y.1, hBQ y.2⟩ = M.toHomUnits ⟨b₀, hb₀⟩ := Units.ext hy
        have hz1 : M.toHomUnits (⟨(b₀ * x * b₀⁻¹)⁻¹ * (y.1 * x * y.1⁻¹), hBQ hz⟩ :
            ↥(flagStabilizer 5 (ZMod 2) I)) = 1 := by
          have e : (⟨(b₀ * x * b₀⁻¹)⁻¹ * (y.1 * x * y.1⁻¹), hBQ hz⟩ :
              ↥(flagStabilizer 5 (ZMod 2) I)) =
              (⟨b₀, hb₀⟩ * ⟨x, hxQ⟩ * ⟨b₀, hb₀⟩⁻¹)⁻¹ *
                (⟨y.1, hBQ y.2⟩ * ⟨x, hxQ⟩ * ⟨y.1, hBQ y.2⟩⁻¹) := rfl
          rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hΦ]
          group
        have := congrArg Units.val hz1
        simpa using this
    ·
      left
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      have := hno i hi
      have := hI i hi
      omega

end CFSG.Quasithin.A38c8

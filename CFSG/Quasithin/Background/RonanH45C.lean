module

public import CFSG.Quasithin.Background.HFL3Hyp
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH45

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def Hhyp (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 2 2 = 0}
  one_mem' := by simp [mat_one]
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    simp [mat_mul, hX, hY]
  inv_mem' {X} hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    simp [mat_inv, hX]

theorem mem_Hhyp {X : HMod n K} : X ∈ Hhyp n K ↔ mat X 2 2 = 0 := Iff.rfl

theorem isFHyp_Hhyp (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) : (∀ (c : K) (X Y : HMod n K), bar n c = c → X ∈ (Hhyp n K) → mat Y = c • mat X → Y ∈ (Hhyp n K)) ∧ rkIdx (Hhyp n K) = n := by
  refine ⟨fun c X Y _ hX hY => ?_, ?_⟩
  · rw [mem_Hhyp] at hX ⊢
    have e := congrFun (congrFun hY 2) 2
    rw [Matrix.smul_apply, smul_eq_mul, hX, mul_zero] at e
    exact e
  ·
    let f : HMod n K →* Multiplicative K :=
      { toFun := fun X => Multiplicative.ofAdd (mat X 2 2)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hker : f.ker = Hhyp n K := by
      ext X
      exact ⟨fun h => ofAdd_eq_one.mp (MonoidHom.mem_ker.mp h),
        fun h => MonoidHom.mem_ker.mpr (ofAdd_eq_one.mpr h)⟩
    have hfix : ∀ y : f.range, bar n (Multiplicative.toAdd (y : Multiplicative K)) =
        Multiplicative.toAdd (y : Multiplicative K) := by
      rintro ⟨y, X, rfl⟩
      exact herm_apply X 2 2
    let g : f.range → {b : K // bar n b = b} := fun y =>
      ⟨Multiplicative.toAdd (y : Multiplicative K), hfix y⟩
    have hg : Function.Bijective g := by
      constructor
      · intro y y' h
        have h' := congrArg Subtype.val h
        exact Subtype.ext h'
      · intro c
        have hXc : mat (mkH (Matrix.diagonal ![0, 0, c.1])
            (herm_diag (map_zero (bar n)) c.2)) 2 2 = c.1 := by
          simp [mat_mkH]
        exact ⟨⟨Multiplicative.ofAdd c.1, ⟨mkH (Matrix.diagonal ![0, 0, c.1])
          (herm_diag (map_zero (bar n)) c.2), congrArg Multiplicative.ofAdd hXc⟩⟩, Subtype.ext rfl⟩
    have hrange : Nat.card f.range = 2 ^ n := by
      rw [← card_fixed hn hK]
      exact Nat.card_congr (Equiv.ofBijective g hg)
    unfold rkIdx
    rw [← hker, Subgroup.index_ker, hrange, padicValNat.prime_pow]

theorem fixV_le_Hhyp {B : Subgroup (MulAut (HMod n K))} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hB : B ≤ (Q2 K).map (rho hK)) (hB1 : B ≠ ⊥) : fixV B ≤ Hhyp n K := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hB hb)
  obtain ⟨hgU, hg01⟩ := mem_Q2.mp hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hb1 (Subtype.ext (map_one (rho hK)))
  intro Y hY
  have hY' : rho hK g Y = Y := mem_fixV.mp hY _ hb
  obtain ⟨h02, h12, -⟩ := fix_entries_Q2 hK hgU hg01 hY'
  rw [mem_Hhyp]
  by_cases h0 : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0
  · by_cases h1 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0
    · exact absurd (uni3_ext hgU (one_mem _) (by simp [hg01]) (by simp [h0]) (by simp [h1])) hg1
    · exact (mul_eq_zero.mp h12).resolve_left h1
  · exact (mul_eq_zero.mp h02).resolve_left h0

private theorem sq_eq_one_of_Q2 {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ Q2 K) :
    g ^ 2 = 1 := by
  obtain ⟨hgU, hg01⟩ := mem_Q2.mp hg
  rw [sq]
  apply uni3_ext (mul_mem hgU hgU) (one_mem _)
  · rw [uni3_mul_01 hgU hgU, hg01]
    simp
  · rw [uni3_mul_02 hgU hgU, hg01, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    simp
  · rw [uni3_mul_12 hgU hgU, CharTwo.add_self_eq_zero]
    simp

theorem gammaCheck_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hAQ : A ≤ (Q2 K).map (rho hK))
    (hcard : 2 ^ (3 * n) < Nat.card A) : E3.gammaCheck (3 * n) A = Hhyp n K := by
  have hA2 : IsPGroup 2 A := by
    intro x
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp (hAQ x.2)
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    change (x : MulAut (HMod n K)) ^ 2 = 1
    rw [← hgx, ← map_pow, sq_eq_one_of_Q2 hg, map_one]
  apply le_antisymm
  · refine iSup_le fun X => iSup_le fun hXA => iSup_le fun hXk => ?_
    refine fixV_le_Hhyp hK (hXA.trans hAQ) ?_
    rintro rfl
    have hcardA := E3.card_eq_two_pow_mul hA2 (bot_le : (⊥ : Subgroup (MulAut (HMod n K))) ≤ A)
    rw [Subgroup.card_bot, mul_one] at hcardA
    have hle : Nat.card A ≤ 2 ^ (3 * n) := by
      rw [hcardA]
      exact Nat.pow_le_pow_right (by norm_num) hXk
    exact absurd hcard (not_lt.mpr hle)
  · intro X hX
    obtain ⟨P, hPdef⟩ : ∃ P : Subgroup (SpecialLinearGroup (Fin 3) K),
        P = A.comap (rho hK) ⊓ Q2 K := ⟨_, rfl⟩
    have hmemP : ∀ x, x ∈ P ↔ rho hK x ∈ A ∧ x ∈ Q2 K := by
      intro x
      rw [hPdef, Subgroup.mem_inf, Subgroup.mem_comap]
    have hPU : P ≤ unitriangular 3 K := fun x hx => (mem_Q2.mp ((hmemP x).mp hx).2).1
    have hP01 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
      fun x hx => (mem_Q2.mp ((hmemP x).mp hx).2).2
    have hinj : ∀ x ∈ P, rho hK x = 1 → x = 1 := fun x hx h => eq_one_of_rho_uni3 hK (hPU hx) h
    have hPmap : P.map (rho hK) = A := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact ((hmemP x).mp hx).1
      · intro a ha
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hAQ ha)
        exact Subgroup.mem_map.mpr ⟨g, (hmemP g).mpr ⟨ha, hg⟩, rfl⟩
    have hcardP : 2 ^ (3 * n) < Nat.card P := by
      rw [← card_map_rho_of_inj hK hinj, hPmap]
      exact hcard
    have hXm := mem_gammaCheck_of_Q2 hn hK hPU hP01 hinj hcardP (mem_Hhyp.mp hX)
    rwa [hPmap] at hXm

private theorem eq_one_of_fix_Hhyp (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ Q2 K)
    (h : ∀ X : HMod n K, mat X 2 2 = 0 → rho hK g X = X) : g = 1 := by
  obtain ⟨hgU, hg01⟩ := mem_Q2.mp hg
  obtain ⟨g00, g11, g22, g10, g20, g21⟩ := uni3_entries hgU
  have h02 : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    by_contra hβ
    obtain ⟨a, ha⟩ : ∃ a : K, a * (g : Matrix (Fin 3) (Fin 3) K) 0 2 +
        bar n (a * (g : Matrix (Fin 3) (Fin 3) K) 0 2) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hβ (eq_zero_of_trace hn hK hcon)
    have hM : (conjM n !![(0 : K), 0, bar n a; 0, 0, 0; a, 0, 0])ᵀ =
        !![(0 : K), 0, bar n a; 0, 0, 0; a, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, bar_bar hK]
    have hX := h (mkH _ hM) (by simp [mat_mkH])
    have e := congrFun (congrFun (congrArg mat hX) 0) 0
    simp [mat_rho, mat_mkH, tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, g00, g10, g20,
      hg01] at e
    apply ha
    simp only [map_mul]
    linear_combination e
  have h12 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    by_contra hβ
    obtain ⟨a, ha⟩ : ∃ a : K, a * (g : Matrix (Fin 3) (Fin 3) K) 1 2 +
        bar n (a * (g : Matrix (Fin 3) (Fin 3) K) 1 2) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hβ (eq_zero_of_trace hn hK hcon)
    have hM : (conjM n !![(0 : K), 0, 0; 0, 0, bar n a; 0, a, 0])ᵀ =
        !![(0 : K), 0, 0; 0, 0, bar n a; 0, a, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, bar_bar hK]
    have hX := h (mkH _ hM) (by simp [mat_mkH])
    have e := congrFun (congrFun (congrArg mat hX) 1) 1
    simp [mat_rho, mat_mkH, tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, g11, g10, g21,
      g20] at e
    apply ha
    simp only [map_mul]
    linear_combination e
  apply uni3_ext hgU (one_mem _)
  · simp [hg01]
  · simp [h02]
  · simp [h12]

theorem eq_bot_of_Hhyp_le_fixV (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {B : Subgroup (MulAut (HMod n K))} (hB : B ≤ (Q2 K).map (rho hK))
    (h : Hhyp n K ≤ fixV B) : B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hB hb)
  have hg1 : g = 1 := eq_one_of_fix_Hhyp hn hK hg fun X hX => mem_fixV.mp (h (mem_Hhyp.mpr hX)) _ hb
  rw [hg1, map_one]

end CFSG.Quasithin.RonanH45

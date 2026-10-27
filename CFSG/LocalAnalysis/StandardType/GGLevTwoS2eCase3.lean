module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxOut

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2e_neg_sigma_pm {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n)
    (c : Fin n → ZMod p) (c₀ : ZMod p) (a : Fin n) :
    -(levTwoS2d_sigma n hn c c₀ a) = 1 ∨ -(levTwoS2d_sigma n hn c c₀ a) = -1 :=
  levTwoS2d_neg_sign (levTwoS2d_sigma_pm n hn c c₀ a)

theorem levTwoS2e_ofCoord_swap (n : ℕ) {i j : Fin n} (hij : i ≠ j) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    levTwoS2d_ofCoord n i j s t hij hs ht =
      levTwoS2d_ofCoord n j i t s (Ne.symm hij) ht hs := by
  apply toStdD_injective n
  rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm]

theorem levTwoS2e_mem_Phi_sub {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p}
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {a b : Fin n} (hab : a ≠ b) :
    levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a) (-(levTwoS2d_sigma n hn c c₀ b))
      hab (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2e_neg_sigma_pm n hn c c₀ b) ∈ Φ := by
  rw [levTwoS2d_mem_Phi_iff n hn hp2 c hΦ hab (levTwoS2d_sigma_pm n hn c c₀ a)
      (levTwoS2e_neg_sigma_pm n hn c c₀ b)
      (levTwoS2d_ofCoord_toStdD n a b (levTwoS2d_sigma n hn c c₀ a)
        (-(levTwoS2d_sigma n hn c c₀ b)) hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2e_neg_sigma_pm n hn c c₀ b))]
  have ha := levTwoS2d_sigma_spec n hn c (hd a)
  have hb := levTwoS2d_sigma_spec n hn c (hd b)
  have hsa : ((levTwoS2d_sigma n hn c c₀ a : ℤ) : ZMod p) *
      ((levTwoS2d_sigma n hn c c₀ a : ℤ) : ZMod p) = 1 := by
    rcases levTwoS2d_sigma_pm n hn c c₀ a with h | h <;> simp [h]
  have hsb : ((levTwoS2d_sigma n hn c c₀ b : ℤ) : ZMod p) *
      ((levTwoS2d_sigma n hn c c₀ b : ℤ) : ZMod p) = 1 := by
    rcases levTwoS2d_sigma_pm n hn c c₀ b with h | h <;> simp [h]
  rw [← ha, ← hb]
  simp only [Int.cast_neg]
  linear_combination c₀ * hsa - c₀ * hsb

theorem levTwoS2e_pair_step {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p}
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {S : Set (Fin n → ℤ)} (hS : Φ ⊆ S) {a b c' : Fin n}
    (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c')
    (hx : Cl (isFiniteType_cartanD n) S
      (levTwoS2d_ofCoord n a c' (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ c')
        hac (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ c'))) :
    Cl (isFiniteType_cartanD n) S
      (levTwoS2d_ofCoord n b c' (levTwoS2d_sigma n hn c c₀ b) (levTwoS2d_sigma n hn c c₀ c')
        hbc (levTwoS2d_sigma_pm n hn c c₀ b) (levTwoS2d_sigma_pm n hn c c₀ c')) := by
  have hmem := levTwoS2e_mem_Phi_sub n hn hp2 c hΦ hd hab
  have hcl := Cl.refl (Cl.base (hS hmem)) hx
  have hEq : weylAction (isFiniteType_cartanD n)
        (rRefl (isFiniteType_cartanD n)
          (levTwoS2d_ofCoord n a b (levTwoS2d_sigma n hn c c₀ a)
            (-(levTwoS2d_sigma n hn c c₀ b)) hab (levTwoS2d_sigma_pm n hn c c₀ a)
            (levTwoS2e_neg_sigma_pm n hn c c₀ b)))
        (levTwoS2d_ofCoord n a c' (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ c')
          hac (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ c')) =
      levTwoS2d_ofCoord n b c' (levTwoS2d_sigma n hn c c₀ b) (levTwoS2d_sigma n hn c c₀ c')
        hbc (levTwoS2d_sigma_pm n hn c c₀ b) (levTwoS2d_sigma_pm n hn c c₀ c') := by
    apply toStdD_injective n
    rw [levTwoS2d_toStdD_rRefl_gen n hn hab (levTwoS2d_sigma_pm n hn c c₀ a)
        (levTwoS2e_neg_sigma_pm n hn c c₀ b)
        (levTwoS2d_ofCoord n a c' (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ c')
          hac (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ c')),
      levTwoS2d_ofCoord_toStdD n a c' (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ c')
        hac (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ c'),
      levTwoS2d_ofCoord_toStdD n b c' (levTwoS2d_sigma n hn c c₀ b) (levTwoS2d_sigma n hn c c₀ c')
        hbc (levTwoS2d_sigma_pm n hn c c₀ b) (levTwoS2d_sigma_pm n hn c c₀ c')]
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rcases levTwoS2d_sigma_pm n hn c c₀ a with ha | ha <;>
      rcases levTwoS2d_sigma_pm n hn c c₀ b with hb | hb <;>
      rcases levTwoS2d_sigma_pm n hn c c₀ c' with hc | hc <;>
      simp_all <;> split_ifs <;> simp_all
  rwa [hEq] at hcl

theorem levTwoS2e_pair_reach {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {c₀ : ZMod p}
    (hd : ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀)
    {S : Set (Fin n → ℤ)} (hS : Φ ⊆ S) {a e : Fin n} (hae : a ≠ e)
    (hx : Cl (isFiniteType_cartanD n) S
      (levTwoS2d_ofCoord n a e (levTwoS2d_sigma n hn c c₀ a) (levTwoS2d_sigma n hn c c₀ e)
        hae (levTwoS2d_sigma_pm n hn c c₀ a) (levTwoS2d_sigma_pm n hn c c₀ e))) :
    ∀ (b d : Fin n) (hbd : b ≠ d),
      Cl (isFiniteType_cartanD n) S
        (levTwoS2d_ofCoord n b d (levTwoS2d_sigma n hn c c₀ b) (levTwoS2d_sigma n hn c c₀ d)
          hbd (levTwoS2d_sigma_pm n hn c c₀ b) (levTwoS2d_sigma_pm n hn c c₀ d)) := by
  intro b d hbd
  by_cases hbe : b = e
  · subst b
    by_cases hda : d = a
    · subst d
      convert hx using 1
      apply toStdD_injective n
      rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm]
    · have h1 := levTwoS2e_pair_step n hn hp2 c hΦ hd hS (Ne.symm hda) hae
        (fun h : d = e => hbd h.symm) hx
      convert h1 using 1
      apply toStdD_injective n
      rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm]
  · by_cases hba : b = a
    · subst b
      by_cases hde : d = e
      · subst d
        exact hx
      · have h1 := levTwoS2e_pair_step n hn hp2 c hΦ hd hS (Ne.symm hde) (Ne.symm hae)
          (fun h : d = a => hbd h.symm)
          (by
            convert hx using 1
            apply toStdD_injective n
            rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm])
        convert h1 using 1
        apply toStdD_injective n
        rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm]
    · have h1 := levTwoS2e_pair_step n hn hp2 c hΦ hd hS (Ne.symm hba) hae hbe hx
      by_cases hde : d = e
      · subst d
        exact h1
      · have h2 := levTwoS2e_pair_step n hn hp2 c hΦ hd hS (Ne.symm hde)
          (fun h : e = b => hbe h.symm) (Ne.symm hbd)
          (by
            convert h1 using 1
            apply toStdD_injective n
            rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm])
        convert h2 using 1
        apply toStdD_injective n
        rw [levTwoS2d_ofCoord_toStdD, levTwoS2d_ofCoord_toStdD, add_comm]

end CFSG.StandardType.LevTwo

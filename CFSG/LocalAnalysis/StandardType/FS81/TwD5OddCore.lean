module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvOrthOff
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Fus

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix

theorem orth_eq_bot_twD5 {Xg Mg : Subgroup (GL (Fin (5 + 1)) (ZMod 3))}
    (hC : ∀ x ∈ Xg, (x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → (x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) ∈ monoFix0 5)
    (hW : ∀ A ∈ evenFix0 5, ∃ x ∈ Xg, (x : Matrix (Fin (5 + 1)) (Fin (5 + 1)) (ZMod 3)) = A)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1) : Mg = ⊥ := by
  set T₁ : Finset (Fin (5 + 1)) := {1, 2, 3, 4} with hT₁
  set T₂ : Finset (Fin (5 + 1)) := {2, 3, 4, 5} with hT₂
  obtain ⟨s₁, hs₁X, hs₁⟩ := hW _ (sgnOn_mem_evenFix0 T₁ (by decide) (by decide))
  obtain ⟨s₂, hs₂X, hs₂⟩ := hW _ (sgnOn_mem_evenFix0 T₂ (by decide) (by decide))
  obtain ⟨z₁, hz₁X, hz₁⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 2 5) (by decide))
  obtain ⟨z₂, hz₂X, hz₂⟩ :=
    hW _ (perm_mem_evenFix0 (Equiv.swap 1 3 * Equiv.swap 4 5) (by decide))
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₁ (by decide) (by decide))
  have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₂ (by decide) (by decide))
  have hinv₁ : ∀ m ∈ Mg, s₁ * m * s₁⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 5) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₁X
      (gl_mul_self hs₁ (by decide) (by decide)) (by rw [hs₁]; exact spMat_mulVec_e0 rfl rfl)
      (w := Pi.single 5 1) (fun v hv => by
        rw [hs₁] at hv
        have hz : ∀ i ∈ T₁, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, v 5, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₁]) hm
  have hinv₂ : ∀ m ∈ Mg, s₂ * m * s₂⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 5) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₂X
      (gl_mul_self hs₂ (by decide) (by decide)) (by rw [hs₂]; exact spMat_mulVec_e0 rfl rfl)
      (w := Pi.single 1 1) (fun v hv => by
        rw [hs₂] at hv
        have hz : ∀ i ∈ T₂, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, v 1, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₂]) hm
  have hc := cent_of_inverts hinv₁ hinv₂
  have hprod := cent_mul (cent_conj hMn hc hz₁X) (cent_conj hMn hc hz₂X)
  have hword : z₁ * (s₁ * s₂) * z₁⁻¹ * (z₂ * (s₁ * s₂) * z₂⁻¹) = s₁ := by
    rw [hz₁i, hz₂i]
    apply Units.ext
    simp only [Units.val_mul]
    rw [hs₁, hs₂, hz₁, hz₂]
    simp only [spMat_mul, mul_assoc]
    exact spMat_congr (by decide) (by decide)
  rw [hword] at hprod
  exact eq_bot_of_inverting hp (by omega) hMp hinv₁ hprod

theorem t5TransvAll {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hloc : LocalOrthI B b₀ ∨ LocalOrthII B b₀) (hfus : Fus42 B b₀)
    (hodd : ¬ OddCoreTrivial E) : TransvAll b₀ K E := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, -⟩ := hhyp
  obtain ⟨hdisj, -⟩ := hcanon
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 5 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 5 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  exact transvAll_of_orth (n := 5) (by norm_num) B hB hord hdisj hCm hfus hodd
    (fun {_ _} hC hW hMX hMn hMc {_} hp hp5 hMp =>
      orth_eq_bot_twD5 hC hW hMX hMn hMc hp hp5 hMp)

theorem transvSetup_twD5 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hfus : Fus42 B b₀) (htr : TransvAll b₀ K E) : TransvSetup b₀ K E := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨hdisj, hsup, -, -, hCK⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  have hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    have h := hfus.1
    rwa [hB.1] at h
  exact ⟨hb₀, hEmax.2.1, hsup, hdisj, htr.1, htr.2, fun y hy k hk =>
    fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hCK hEmax.2.1 hnorm hy hk⟩

theorem noTransvData_twD5 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hloc : LocalOrthI B b₀ ∨ LocalOrthII B b₀) (htr : TransvAll b₀ K E) :
    NoTransvData B b₀ K E := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, -⟩ := hhyp
  obtain ⟨hdisj, -, -, hEKcard, -⟩ := hcanon
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 5 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 5 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hsc, hdiag, hct, hd3, hds⟩ := orthSignData (n := 5) (by norm_num) hB hCm
  have hKl : KleinSigns B E := orth_kleinSigns (n := 5) hB hCm
    (s := ![1, -1, -1, -1, -1, 1]) (s' := ![1, 1, 1, 1, -1, -1])
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩ (by decide)
  exact ⟨hsc, hdiag, hct, hKl, hd3, hds, orth_noOffenderA hB hord hdisj hEKcard hCm htr⟩

theorem twoLocalPrimeRank_le_twD5 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) : twoLocalPrimeRank 3 G ≤ 5 + 1 := by
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, hA3, -, -, -, -, -⟩ := hhyp
  obtain ⟨-, -, hEKmax, hEKcard, -⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaMinus_of_marking (r := 5) (by norm_num) hKmark hKz
  have hK3 := (rowFacts_twD5_of_mulEquiv (A := E ⊓ K) φ inf_le_right hEKmax.2.1 hEKcard).1
  have h := twoLocalPrimeRank_C_le hb₀ hKC hKn hKz hOut hA2 hK3
  rwa [← hA3]

theorem exists_acts_swap_twD5 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hloc : LocalOrthI B b₀ ∨ LocalOrthII B b₀) :
    ∃ d ∈ Subgroup.normalizer (E : Set G), B.Acts d (spMat (Equiv.swap 4 5) fun _ => 1) := by
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 5 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 5 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hsp : spMat (Equiv.swap 4 5) (fun _ => 1) ∈
      B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
    rcases hCm with h | h
    · rw [h]
      exact evenFix0_subset_monoFix0 5 (perm_mem_evenFix0 (Equiv.swap 4 5) (by decide))
    · rw [h]
      exact perm_mem_evenFix0 (Equiv.swap 4 5) (by decide)
  obtain ⟨d, -, hd⟩ := hsp
  exact ⟨d, hB.1 ▸ B.mem_normalizer_of_acts hd, hd⟩

theorem t5NoTransv {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hloc : LocalOrthI B b₀ ∨ LocalOrthII B b₀) (hfus : Fus42 B b₀) :
    ¬ TransvAll b₀ K E := by
  intro htr
  obtain ⟨hsc, hdiag, hct, hKl, hd3, -, hoff⟩ := noTransvData_twD5 hstd hB hloc htr
  have h := transvSetup_twD5 hstd hB hfus htr
  have hrank := twoLocalPrimeRank_le_twD5 hstd
  have hsw := exists_acts_swap_twD5 hB hloc
  obtain ⟨hsimple, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, -, -, -, -, -, hEcard, -⟩ := hhyp
  obtain ⟨hdisj, -, -, hEKcard, -⟩ := hcanon
  have hOut := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  obtain ⟨P₁, hP⟩ := h.exists_transvP1'
  obtain ⟨μ, hμ⟩ := hP.exists_cube_eq_pow h B hB hsc hdiag hct
  have hA9 : 9 ≤ Nat.card ↥(E ⊓ K) := by rw [hEKcard]; norm_num
  have hne := hP.not_exp_three_swap h B hB hsc hKl hd3 hA9 (k₀ := 4) (k₁ := 5)
    (by decide) (by decide) (by decide) hsw (by norm_num) hrank
  have hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K) := by rw [hEcard, hEKcard]; norm_num
  have hAbot : E ⊓ K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA9
    omega
  exact hP.false_of_noOffender h B hB hsc hKl hd3 hμ hne hA9 hKC hKn hKz hOut hoff hEA
    (fs81Nt_mem_commutator hsimple hb₀ hdisj hAbot)

theorem t5OddCore_holds :
    ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
      ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → (LocalOrthI B b₀ ∨ LocalOrthII B b₀) →
        Fus42 B b₀ → OddCoreTrivial E := by
  intro G _ _ b₀ K E hstd B hB hloc hfus
  by_contra hodd
  exact t5NoTransv hstd hB hloc hfus (t5TransvAll hstd hB hloc hfus hodd)

end CFSG.StandardType.FrameRoute.FS81

end

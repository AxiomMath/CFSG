module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLField48
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalNormalizerOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16e3_prime_eq_of_dvd_order {p : ℕ} (hp : p.Prime)
    (h : p ∣ 5922201600) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
  have hN : 5922201600 = 2 ^ 13 * 3 ^ 5 * 5 ^ 2 * 7 * 17 := by norm_num
  rw [hN] at h
  have hpow : ∀ {q k : ℕ}, q.Prime → 0 < k → p ∣ q ^ k → p = q := by
    intro q k hq _ hd
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact Or.inl (hpow Nat.prime_two (by norm_num) h)
        · exact Or.inr (Or.inl (hpow Nat.prime_three (by norm_num) h))
      · exact Or.inr (Or.inr (Or.inl (hpow Nat.prime_five (by norm_num) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hpow (q := 7) (k := 1) (by norm_num) (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hpow (q := 17) (k := 1) (by norm_num) (by norm_num) h))))

private theorem s168e3_false_of_sl_four_four_natural_aux
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL : IsSLn (lBar V₀ V hV L) 4 2)
    {K : Type} [fieldK : Field K] [finiteK : Finite K] [fintypeK : Fintype K]
    (hKcard : Nat.card K = 2 ^ 2)
    (hR : (FFModel.nat (StatedSL 4 K)).Realizes (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) : False := by
  classical
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  have hK4f : @Fintype.card K fintypeK = 4 := by
    rw [← @Nat.card_eq_fintype_card K fintypeK]
    exact hK4
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_sl_four_component_field_four_eight c hcomp (Or.inl rfl) hSL
  have hwt : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hR' : (FFModel.nat (StatedSL 4 K)).Realizes (lBar V₀ V hV L) ⊤
      (fixV (lBar V₀ V hV L)) := by
    have h := hR
    rw [hwt, top_inf_eq] at h
    exact h
  have hHnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (lBar_conj_eq_of_s15_eq_one hs hg)
  have hHA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hHn : ∀ a ∈ Mbar D.M V₀ V hV, ∀ h ∈ lBar V₀ V hV L,
      a * h * a⁻¹ ∈ lBar V₀ V hV L := by
    intro a ha h hh
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm ha) h).mp hh
  obtain ⟨ρ, hρinj, hρN⟩ :=
    s16g_exists_embedding (W := Vtil V₀ V hV) (A := Mbar D.M V₀ V hV)
      (H := lBar V₀ V hV L) (Γ := StatedSL 4 K) hHA hHn hR' hwt
  let E : Subgroup (MulAut (Multiplicative (Fin 4 → K))) := ρ.range
  have hEcard : Nat.card E = Nat.card ↥(Mbar D.M V₀ V hV) := by
    change Nat.card (ρ.range) = Nat.card ↥(Mbar D.M V₀ V hV)
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρinj, Subgroup.card_top]
  have hEN : E ≤ s16gNorm (StatedSL 4 K) := by
    rintro x ⟨a, rfl⟩
    exact hρN a
  have hdvdE : Nat.card E ∣ Nat.card (RingAut K) * Nat.card (GL (Fin 4) K) :=
    s16g_card_dvd_of_norm (Γ := StatedSL 4 K)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSL (by norm_num : 2 ≤ 4)) hEN
  have hcardRing : Nat.card (RingAut K) = 2 := by
    simpa using s16k_card_ringAut_of_card (K := K) (a := 2) hKcard
  have hcardGL : Nat.card (GL (Fin 4) K) = 2961100800 := by
    rw [@Matrix.card_GL_field K fieldK fintypeK 4]
    rw [hK4f]
    norm_num [Fin.prod_univ_four]
  have hdvdA : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 5922201600 := by
    rw [← hEcard]
    rw [Nat.card_eq_fintype_card]
    rw [hcardRing] at hdvdE
    rw [hcardGL] at hdvdE
    norm_num at hdvdE
    exact hdvdE
  have hsig : D.sig ⊆ ({3, 5} : Set ℕ) := by
    intro p hpσ
    have hpp : p.Prime := (D.sig_prime p hpσ).1
    have hpodd : p ≠ 2 := (D.sig_prime p hpσ).2
    have hp2dvd : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      obtain ⟨E', hE'A, -, hE'card⟩ :=
        CFSG.SectionRank.exists_pRank hpp.one_lt (Mbar D.M V₀ V hV)
      have h2 : 2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := c.two_le_pRank_mbar hpσ
      have h1 : p ^ 2 ∣ Nat.card ↥E' := by
        rw [hE'card]
        exact pow_dvd_pow p h2
      exact h1.trans (Subgroup.card_dvd_of_le hE'A)
    have hp2N : p ^ 2 ∣ 5922201600 := hp2dvd.trans hdvdA
    have hpN : p ∣ 5922201600 :=
      (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hp2N
    rcases s16e3_prime_eq_of_dvd_order hpp hpN with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hpodd
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num at hp2N
    · norm_num at hp2N
  have hfix3 : S168e3Fix (Mbar D.M V₀ V hV) 3 := by
    intro x hx1
    have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hZ : ∀ h ∈ lBar V₀ V hV L, ∀ z ∈ fixV (lBar V₀ V hV L), h z = z :=
      fun h hh z hz => (mem_fixV.1 hz) h hh
    have hne : ∃ a : Multiplicative (Fin 4 → K), a ≠ 1 := by
      refine ⟨Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : K)), ?_⟩
      intro h
      have h' : (Pi.single (0 : Fin 4) (1 : K)) = (0 : Fin 4 → K) := by
        simpa using congrArg Multiplicative.toAdd h
      have h0 : (1 : K) = 0 := by simpa using congrFun h' (0 : Fin 4)
      exact one_ne_zero h0
    obtain ⟨B, hBH, hBp, hBc, hBfix⟩ :=
      s16g_transport_fix (StatedSL 4 K) hR' hW hZ hne Nat.prime_three (by norm_num)
        (s16g_fixNc_statedSL_torus (n := 4) (by norm_num) Nat.prime_three
          (by norm_num [hK4f])) hx1
    exact ⟨B, hBH.trans hHA, hBp, hBc, hBfix⟩
  have h3not : 3 ∉ D.sig := fun h3 => s168e3_false_of_fix c Nat.prime_three h3 hfix3
  have hfix5 : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 5 ∧ b x = x := by
    intro x hx1
    have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hZ : ∀ h ∈ lBar V₀ V hV L, ∀ z ∈ fixV (lBar V₀ V hV L), h z = z :=
      fun h hh z hz => (mem_fixV.1 hz) h hh
    have hne : ∃ a : Multiplicative (Fin 4 → K), a ≠ 1 := by
      refine ⟨Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : K)), ?_⟩
      intro h
      have h' : (Pi.single (0 : Fin 4) (1 : K)) = (0 : Fin 4 → K) := by
        simpa using congrArg Multiplicative.toAdd h
      have h0 : (1 : K) = 0 := by simpa using congrFun h' (0 : Fin 4)
      exact one_ne_zero h0
    obtain ⟨y, hyH, hyord, hyfix⟩ :=
      s16g_transport_fix_ord (StatedSL 4 K) hR' hW hZ hne Nat.prime_five (by norm_num)
        (s16g_fixOrd_statedSL (n := 4) (by norm_num) Nat.prime_five
          (by norm_num [hK4f])) hx1
    exact ⟨y, hHA hyH, hyord, hyfix⟩
  have hcube : ¬ 5 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h
    have h5 : 5 ^ 3 ∣ 5922201600 := h.trans hdvdA
    norm_num at h5
  have hkern5 : S168e3Kernel (Mbar D.M V₀ V hV) 5 :=
    s168e3_kernel_of_cube Nat.prime_five _ hcube hfix5
  have h5not : 5 ∉ D.sig := fun h5 => s168e3_false_of_kernel c Nat.prime_five h5 hkern5
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  rcases hsig hpσ with hp3 | hp5
  · exact h3not (hp3 ▸ hpσ)
  · exact h5not (hp5 ▸ hpσ)

theorem s168e3_false_of_sl_four_four_natural
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL : IsSLn (lBar V₀ V hV L) 4 2)
    (hN : BinaryNaturalSL (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 4 2) : False := by
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hN
  exact @s168e3_false_of_sl_four_four_natural_aux G _ _ D V₀ V L hV c hcomp hSL K
    hKf hKfin (Fintype.ofFinite K) hKcard hR
end CFSG.LocalAnalysis.UniquenessCase.PartTwo

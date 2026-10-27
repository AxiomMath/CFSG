module

public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSixSimple
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LinearAlgebra.PpdSelfDual
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

theorem isSimpleGroup_statedOmega_quadPlus_three_of_card_two {K : Type} [Field K] [Finite K]
    [CharP K 2] (hcard : Nat.card K = 2) :
    IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 K)) := by
  letI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardF
  let eΩ := CFSG.SeitzReduction.OmegaPilot.statedOmegaPlusCongr φ 3
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isSimpleGroup_statedOmega_quadPlus_three
  exact eΩ.isSimpleGroup

theorem orderOf_two_zmod_eq_five_of_eq_four {r : ℕ} (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4) : r = 5 := by
  have h4 : (2 : ZMod r) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hdvd : r ∣ 2 ^ 4 - 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff 4).2 h4
  have h15 : r ∣ 3 * 5 := by
    norm_num at hdvd ⊢
    exact hdvd
  have hcases : r = 3 ∨ r = 5 := by
    rcases hr.dvd_or_dvd h15 with h3 | h5
    · have := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 h3
      rcases this with h1 | h3'
      · exfalso
        rw [h1] at hr
        exact Nat.not_prime_one hr
      · exact Or.inl h3'
    · have := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h5
      rcases this with h1 | h5'
      · exfalso
        rw [h1] at hr
        exact Nat.not_prime_one hr
      · exact Or.inr h5'
  rcases hcases with rfl | rfl
  · exfalso
    have h3 : orderOf (2 : ZMod 3) = 2 := by
      apply orderOf_eq_prime <;> decide
    omega
  · rfl

theorem exists_commuting_statedOmega_quadPlus_three_zmod_two {r : ℕ} (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * 1) :
    ∃ a b : ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))), a * b = b * a ∧
      orderOf a = r ∧ b ≠ 1 ∧ b ^ (2 ^ 1 + 1) = 1 := by
  have h4 : orderOf (2 : ZMod r) = 4 := by simpa using hord
  have hr5 : r = 5 := orderOf_two_zmod_eq_five_of_eq_four hr h4
  subst hr5
  let e : ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 8)) :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8
  let a8 : ↥(alternatingGroup (Fin 8)) :=
    ⟨c[0, 1, 2, 3, 4], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b8 : ↥(alternatingGroup (Fin 8)) :=
    ⟨c[5, 6, 7], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have ha8pow : a8 ^ 5 = 1 := Subtype.ext (by decide)
  have ha8ne : a8 ≠ 1 := by decide
  have hb8pow : b8 ^ 3 = 1 := Subtype.ext (by decide)
  have hb8ne : b8 ≠ 1 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha8 : orderOf a8 = 5 := orderOf_eq_prime ha8pow ha8ne
  have hb8 : orderOf b8 = 3 := orderOf_eq_prime hb8pow hb8ne
  refine ⟨e.symm a8, e.symm b8, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by decide)
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective a8).trans ha8
  · intro hb
    have h1 : b8 = 1 := by
      rw [← e.apply_symm_apply b8, hb, map_one]
    exact hb8ne h1
  · rw [show 2 ^ 1 + 1 = 3 by norm_num, ← map_pow, hb8pow, map_one]

theorem exists_commuting_statedOmega_quadPlus_three_of_field_card_two {K : Type} [Field K]
    [Finite K] [CharP K 2] {f r : ℕ} (hK : Nat.card K = 2 ^ f) (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f) (hf : f = 1) :
    ∃ a b : ↥(StatedOmega (StatedQuadPlus 3 K)), a * b = b * a ∧ orderOf a = r ∧ b ≠ 1 ∧
      b ^ (2 ^ f + 1) = 1 := by
  subst hf
  have hcard : Nat.card K = 2 := by simpa using hK
  letI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardF
  let eΩ := CFSG.SeitzReduction.OmegaPilot.statedOmegaPlusCongr φ 3
  obtain ⟨a0, b0, hcomm, ha0, hb0, hbp0⟩ :=
    exists_commuting_statedOmega_quadPlus_three_zmod_two hr hord
  refine ⟨eΩ.symm a0, eΩ.symm b0, ?_, ?_, ?_, ?_⟩
  · apply eΩ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hcomm
  · exact (orderOf_injective eΩ.symm.toMonoidHom eΩ.symm.injective a0).trans ha0
  · intro hb
    have h1 : b0 = 1 := by
      rw [← eΩ.apply_symm_apply b0, hb, map_one]
    exact hb0 h1
  · rw [← map_pow, hbp0, map_one]

theorem det_pow_natCard_sub_one {K : Type} [Field K] [Finite K] (g : GL (Fin 4) K) :
    ((g ^ (Nat.card K - 1) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have hq1 : Nat.card K - 1 = Nat.card Kˣ := (Nat.card_units K).symm
  have hunit : Matrix.GeneralLinearGroup.det g ^ (Nat.card K - 1) = 1 := by
    rw [hq1]
    exact pow_card_eq_one'
  have hdet : Matrix.GeneralLinearGroup.det (g ^ (Nat.card K - 1)) = 1 := by
    rw [map_pow, hunit]
  calc ((g ^ (Nat.card K - 1) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det
      = ↑(Matrix.GeneralLinearGroup.det (g ^ (Nat.card K - 1))) :=
        (Matrix.GeneralLinearGroup.val_det_apply (R := K) _).symm
    _ = 1 := by rw [hdet, Units.val_one]

theorem orderOf_pow_natCard_sub_one_GL_four {K : Type} [Field K] [Finite K]
    (g : GL (Fin 4) K) (hg : orderOf g = Nat.card K ^ 4 - 1) :
    orderOf (g ^ (Nat.card K - 1)) = (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq1 : 1 ≤ Nat.card K := by omega
  have hq4 : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow 4 _ (by omega)
  have hdvd : Nat.card K - 1 ∣ Nat.card K ^ 4 - 1 := by
    refine ⟨Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1, ?_⟩
    zify [hq1, hq4]
    ring
  rw [orderOf_pow_of_dvd (by omega) (by rw [hg]; exact hdvd), hg]
  have hfac : Nat.card K ^ 4 - 1 =
      ((Nat.card K + 1) * (Nat.card K ^ 2 + 1)) * (Nat.card K - 1) := by
    zify [hq1, hq4]
    ring
  exact Nat.div_eq_of_eq_mul_left (by omega : 0 < Nat.card K - 1) hfac

theorem exists_commuting_powers_of_orderOf_eq_mul {G : Type} [Group G] {q r : ℕ}
    (hq : 1 ≤ q) (x : G) (hxord : orderOf x = (q + 1) * (q ^ 2 + 1))
    (hrq : r ∣ q ^ 2 + 1) :
    ∃ a b : G, a * b = b * a ∧ orderOf a = r ∧ b ≠ 1 ∧ b ^ (q + 1) = 1 := by
  let N := (q + 1) * (q ^ 2 + 1)
  have hx : orderOf x ≠ 0 := by
    rw [hxord]
    positivity
  have hrN : r ∣ N := by
    dsimp [N]
    exact Dvd.dvd.mul_left hrq (q + 1)
  let a : G := x ^ (N / r)
  let b : G := x ^ (N / (q + 1))
  have haord : orderOf a = r := by
    have hNr : N / r = orderOf x / r := by rw [hxord]
    dsimp [a]
    rw [hNr]
    exact orderOf_pow_orderOf_div hx (by rwa [hxord])
  have hbord : orderOf b = q + 1 := by
    have hNe : N / (q + 1) = orderOf x / (q + 1) := by rw [hxord]
    dsimp [b]
    rw [hNe]
    exact orderOf_pow_orderOf_div hx (by rw [hxord]; exact dvd_mul_right _ _)
  refine ⟨a, b, ?_, haord, ?_, ?_⟩
  · dsimp [a, b]
    rw [← pow_add, ← pow_add, Nat.add_comm]
  · intro hb
    have : orderOf b = 1 := orderOf_eq_one_iff.mpr hb
    rw [hbord] at this
    omega
  · rw [← hbord]
    exact pow_orderOf_eq_one b

theorem exists_commuting_ppd_statedSL_four {K : Type} [Field K] [Finite K]
    {f r : ℕ} (hK : Nat.card K = 2 ^ f) (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f) (hf : 2 ≤ f) :
    ∃ a b : ↥(StatedSL 4 K), a * b = b * a ∧ orderOf a = r ∧ b ≠ 1 ∧
      b ^ (2 ^ f + 1) = 1 := by
  let q := Nat.card K
  have hqeq : q = 2 ^ f := hK
  have hrq : r ∣ q ^ 2 + 1 := by
    have h := CFSG.LinearAlgebra.PpdSelfDual.dvd_two_pow_add_one_of_orderOf_two hr hord (by omega)
    rw [hqeq]
    rw [show (2 ^ f) ^ 2 + 1 = 2 ^ (2 * f) + 1 by
      rw [show (2 ^ f) ^ 2 = 2 ^ (2 * f) by rw [show 2 * f = f * 2 by ring, pow_mul]]]
    exact h
  obtain ⟨Z, hZcyc, hZcard⟩ := CFSG.SectionRank.OddCover.exists_isCyclic_card_GL K 4
  haveI : IsCyclic Z := hZcyc
  obtain ⟨gZ, hgZ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Z)
  let g : GL (Fin 4) K := (gZ : Z)
  have hg : orderOf g = q ^ 4 - 1 :=
    (orderOf_injective (Subgroup.subtype Z) Z.subtype_injective gZ).trans
      (hgZ.trans hZcard)
  let h : GL (Fin 4) K := g ^ (q - 1)
  have hdet : ((h : Matrix (Fin 4) (Fin 4) K)).det = 1 :=
    det_pow_natCard_sub_one g
  let hSL : ↥(StatedSL 4 K) := ⟨h, Subgroup.subset_closure hdet⟩
  have hSLord : orderOf hSL = (q + 1) * (q ^ 2 + 1) := by
    have hh := orderOf_pow_natCard_sub_one_GL_four g (by rw [hg])
    have h1 : orderOf hSL = orderOf h :=
      (orderOf_injective (Subgroup.subtype (StatedSL 4 K))
        (Subgroup.subtype_injective _) hSL).symm
    rw [h1, show h = g ^ (q - 1) from rfl, hh]
  have hq1 : 1 ≤ q := by
    rw [hqeq]
    exact Nat.one_le_pow f 2 (by norm_num)
  obtain ⟨a, b, hcomm, ha, hb, hbp⟩ :=
    exists_commuting_powers_of_orderOf_eq_mul hq1 hSL hSLord hrq
  refine ⟨a, b, hcomm, ha, hb, ?_⟩
  simpa [hqeq] using hbp

theorem isSimpleGroup_statedOmega_quadPlus_three_of_charTwo {K : Type} [Field K] [Finite K]
    [CharP K 2] : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 K)) := by
  by_cases hK4 : 4 ≤ Nat.card K
  · exact sec7_isSimpleGroup_omegaPlusSix hK4
  · have hcard : Nat.card K = 2 := by
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      have hn1 : (n : ℕ) = 1 := by
        have hle : 2 ^ (n : ℕ) ≤ 3 := by
          rw [← hn, ← Nat.card_eq_fintype_card]
          omega
        have hpos : 0 < (n : ℕ) := n.pos
        by_contra hne
        have h2 : 2 ≤ (n : ℕ) := by omega
        have h4 : 4 ≤ 2 ^ (n : ℕ) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
        omega
      rw [Nat.card_eq_fintype_card, hn, hn1]
      norm_num
    exact isSimpleGroup_statedOmega_quadPlus_three_of_card_two hcard

theorem exists_commuting_ppd_statedOmega_quadPlus_three {K : Type} [Field K] [Finite K]
    [CharP K 2] {f r : ℕ} (hK : Nat.card K = 2 ^ f) (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = 4 * f) :
    ∃ a b : ↥(StatedOmega (StatedQuadPlus 3 K)), a * b = b * a ∧ orderOf a = r ∧ b ≠ 1 ∧
      b ^ (2 ^ f + 1) = 1 := by
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, hf0] at h1
    norm_num at h1
  rcases (by omega : f = 1 ∨ 2 ≤ f) with hf | hf
  · exact exists_commuting_statedOmega_quadPlus_three_of_field_card_two hK hr hord hf
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨e⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv hK4
    obtain ⟨a', b', hcomm, ha, hb, hbp⟩ :=
      exists_commuting_ppd_statedSL_four hK hr hord hf
    refine ⟨e.symm a', e.symm b', ?_, ?_, ?_, ?_⟩
    · apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hcomm
    · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective a').trans ha
    · intro hb'
      have h1 : b' = 1 := by
        rw [← e.apply_symm_apply b', hb', map_one]
      exact hb h1
    · rw [← map_pow, hbp, map_one]

end CFSG.RankThree.GF2n.Stroth80

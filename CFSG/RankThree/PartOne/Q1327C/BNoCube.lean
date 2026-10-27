module

public import CFSG.RankThree.PartOne.N143X.G2Rank
public import CFSG.RankThree.PartOne.N143X.TrialityRank
public import CFSG.RankThree.PartOne.N143X.ReeRank

public section

namespace CFSG.RankThree.PartOne.Q1327C

section

open CFSG.RankThree.PartOne.N143X CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KFU

theorem false_of_pow_three_G2_five
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card K) {E : Subgroup (adjointGroup .G2 K)} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvdC : p ∣ Nat.card (adjointGroup .G2 K) := by
    have : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E)
  rw [card_adjointGroup_G2, CFSG.Open.ordG2] at hdvdC
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (Nat.card K : ℤ) := ⟨_, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvdZ : (p : ℤ) ∣ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h := Int.natCast_dvd_natCast.2 hdvdC
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h
    rw [hQ]
    exact h
  have hqZ : ¬ (p : ℤ) ∣ Q := fun h => hpq (by rw [hQ] at h; exact_mod_cast h)
  have hfac : Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) = Q ^ 6 * ((Q - 1) * (Q + 1) *
      ((Q ^ 2 + Q + 1) * (Q ^ 2 - Q + 1))) * ((Q - 1) * (Q + 1)) := by ring
  rw [hfac] at hdvdZ
  have key : (p : ℤ) ∣ Q - 1 ∨ (p : ℤ) ∣ Q + 1 ∨ (p : ℤ) ∣ Q ^ 2 + Q + 1 ∨
      (p : ℤ) ∣ Q ^ 2 - Q + 1 := by
    rcases hpZ.dvd_or_dvd hdvdZ with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact absurd (hpZ.dvd_of_dvd_pow h) hqZ
      · rcases hpZ.dvd_or_dvd h with h | h
        · rcases hpZ.dvd_or_dvd h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases hpZ.dvd_or_dvd h with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases key with h | h | h | h
  ·
    have hpq1 : p ∣ Nat.card K - 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hq1]
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    have h1 := card_le_sq_of_conj_into_Tp K hp (by omega) hpq1 E hE
    rw [hcard] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  ·
    have hpd : p ∣ Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, ψ, hψ, hT⟩ := exists_torus_negOne_G2 K
    exact false_of_pow_three_of_torus hp (not_dvd_index_of_card_negOne K hp (by omega) hpd T hT) ψ
      hψ hE hcard
  ·
    have hd : ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 2 - 3) * Nat.card K + 1 := by push_cast; ring
    have hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 2) (Or.inr rfl) g2rot_two_g2a
      g2rot_two_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_pow_three_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 2) (Or.inr rfl) _ hd hp (by omega) hpd T hTcard) hE hcard
  ·
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
    have hd : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 1 - 3) * Nat.card K + 1 := by
      push_cast [Nat.cast_sub hle]
      ring
    have hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hle]
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 1) (Or.inl rfl) g2rot_one_g2a
      g2rot_one_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_pow_three_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 1) (Or.inl rfl) _ hd hp (by omega) hpd T hTcard) hE hcard

end

section

open CFSG.RankThree.PartOne.N143X CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.KFU

theorem false_of_pow_three_triality_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  classical
  have hf : 1 ≤ f := hX.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hpT : p ∣ Nat.card X := by
    have : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨hrow, -, -⟩ := exact_E_type_and_triality_cross_prime_factor_exhaustion (ℓ := 2) (f := f)
    hp (by omega) (by omega) hX
  obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 f := hdvd
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hX.2
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  set E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := E.map e.toMonoidHom
    with hE'def
  have hE' : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (e y) ^ p = 1
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hcard]
  have hchar : CharP (AlgebraicClosure K) 2 :=
    charP_algebraicClosure_two (K := K) (g := f * 3) (by rw [hK', ← pow_mul])
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  ·
    have hpq : p ∣ 2 ^ f - 1 := by
      rw [cycloVal_one] at hd
      have h1 : (p : ℤ) ∣ ((2 ^ f - 1 : ℕ) : ℤ) := by rw [Nat.cast_sub hq1]; exact hd
      exact_mod_cast h1
    have hD : D4Param p f K σ.toRingHom := ⟨hp, by omega, hf, hK', fun c => hσ c, hpq⟩
    have := card_le_sq_of_split hD E' hE'
    omega
  ·
    rw [cycloVal_two] at hd
    have := card_le_sq_of_qplus (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ hp (by omega) hd hE'
    omega
  ·
    rw [cycloVal_three] at hd
    have := card_le_sq_of_threeSix (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ (ε := 1)
      (Or.inl rfl) hp (by omega) (by simpa using hd) hE'
    omega
  ·
    rw [cycloVal_six] at hd
    have := card_le_sq_of_threeSix (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ (ε := -1)
      (Or.inr rfl) hp (by omega) (by simpa [sub_eq_add_neg] using hd) hE'
    omega
  ·
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 := by
      have h24 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    exact false_of_pow_three_twelve Nat.prime_two hf hK' σ hσ hp (by omega) hpd hE' hcard'

end

section

open CFSG.RankThree.PartOne.N143X CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KFU CFSG.RankThree.LargeReeOrder

theorem false_of_pow_three_ree_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  classical
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  set E' : Subgroup ↥(ReeTag.F4.reeGamma K a) := E.map e.toMonoidHom with hE'def
  have hE' : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (e y) ^ p = 1
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hcard]
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
    have : p ∣ Nat.card E' := by rw [hcard']; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E')
  have hle : ReeTag.F4.reeGamma K a ≤ adjointGroup .F4 K := Subgroup.map_subtype_le _
  let i : ↥(ReeTag.F4.reeGamma K a) →* ↥(adjointGroup .F4 K) := Subgroup.inclusion hle
  have hi : Function.Injective i := fun x y h => by
    have h' : (i x : ModGL .F4 K) = (i y : ModGL .F4 K) := congrArg Subtype.val h
    exact Subtype.ext h'
  set E₀ : Subgroup ↥(adjointGroup .F4 K) := E'.map i with hE₀def
  have hE₀ : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (i y) ^ p = 1
    rw [← map_pow, hE' y hy, map_one]
  have hcard₀ : Nat.card E₀ = p ^ 3 := by
    rw [hE₀def, Subgroup.card_map_of_injective hi, hcard']
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').2 p hp (by omega)
    hdvd with h1 | h2 | h3 | h4 | h5
  ·
    have hD : F4Param p a K := ⟨hp, by omega, hK', h1⟩
    have := card_le_sq_of_reeSplit hD E' hE'
    omega
  ·
    obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
    have : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    have := card_le_sq_of_sector D (odd_mPhi2' a) (torusParam_phi2 D.isFrob) hp
      (pow_factorization_card_reeGamma_dvd_phi2 hK' hp (by omega) h2) hE'
    omega
  ·
    have := card_le_sq_of_F4_phiFour K hp (by omega) (by rw [hK']; exact h3) hE₀
    omega
  ·
    have := card_le_sq_of_F4_phiSix K hp (by omega) (by rw [hK']; exact h4) hE₀
    omega
  ·
    exact false_of_pow_three_F4_twelve K hp (by omega) (by rw [hK']; exact h5) hE₀ hcard₀

end

end CFSG.RankThree.PartOne.Q1327C

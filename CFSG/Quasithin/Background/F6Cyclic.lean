module

public import CFSG.Quasithin.Background.F6Noncyclic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem openPCore_eq_pCore (p : ℕ) [Fact p.Prime] : Open.pCore p D = CFSG.pCore p D :=
  (CFSG.pCore_eq_open D p).symm

omit [Finite D] in
theorem perm_three_inv : ∀ σ τ : Equiv.Perm (Fin 3), (σ ^ 2 = 1 ∧ σ ≠ 1 ∧ τ ^ 3 = 1) →
    σ * τ * σ⁻¹ * τ = 1 := by
  decide +kernel

omit [Finite D] in
theorem conjNormal_eq_one_of_isCyclic [Finite D] (h : IsGoldschmidtTriple G₁ G₂)
    {X : Subgroup D} [X.Normal] [IsCyclic ↥X] {x : D} (hx : x ∈ G₁) (hx3 : x ^ 3 = 1) :
    (MulAut.conjNormal x : MulAut ↥X) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient₁
  obtain ⟨tq, htq⟩ := e.surjective (Equiv.swap 0 1)
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tq
  have hσ : (e (QuotientGroup.mk (⟨x, hx⟩ : ↥G₁))) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥G₁) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one, map_one]
  have hinv : (t : D) * x * (t : D)⁻¹ * x ∈ pCoreOf 2 G₁ := by
    have h1 : e (QuotientGroup.mk (t * ⟨x, hx⟩ * t⁻¹ * ⟨x, hx⟩)) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, htq]
      exact perm_three_inv _ _ ⟨by decide, by decide, hσ⟩
    have h2 : t * ⟨x, hx⟩ * t⁻¹ * ⟨x, hx⟩ ∈ Open.pCore 2 ↥G₁ := by
      rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
      exact h1
    exact ⟨_, h2, rfl⟩
  set ρ : D →* MulAut ↥X := MulAut.conjNormal with hρ
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁) ⟨_, hinv⟩
  have hk' : ρ ((t : D) * x * (t : D)⁻¹ * x) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : ((t : D) * x * (t : D)⁻¹ * x) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    rw [this, map_one]
  have hcomm : ρ ((t : D) * x * (t : D)⁻¹ * x) = ρ x ^ 2 := by
    rw [map_mul, map_mul, map_mul, map_inv, mulAut_comm_of_isCyclic (ρ t) (ρ x),
      mul_assoc (ρ x), mul_inv_cancel, mul_one, pow_two]
  rw [hcomm] at hk'
  have h3 : ρ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hd2 : orderOf (ρ x ^ 2) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd3 : orderOf (ρ x ^ 2) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul, mul_comm, pow_mul, h3, one_pow])
  have hsq : ρ x ^ 2 = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left hd3 (Nat.Coprime.pow_right k (by norm_num))) hd2)
  calc ρ x = ρ x ^ 3 * (ρ x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hsq, inv_one, one_mul]

theorem twoResidual_le_centralizer_of_isCyclic (h : IsGoldschmidtTriple G₁ G₂)
    {X : Subgroup D} [X.Normal] (hX : IsCyclic ↥X) :
    twoResidual (⊤ : Subgroup D) ≤ Subgroup.centralizer (X : Set D) := by
  have key : ∀ {G G' : Subgroup D}, IsGoldschmidtTriple G G' →
      twoResidual G ≤ Subgroup.centralizer (X : Set D) := by
    intro G G' hG
    rw [twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hx3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd hG hx.1 hx.2)
    have h1 := conjNormal_eq_one_of_isCyclic hG (X := X) hx.1 hx3
    show x ∈ Subgroup.centralizer (X : Set D)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun α : MulAut ↥X => ((α ⟨y, hy⟩ : ↥X) : D)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc y * x = x * y * x⁻¹ * x := by rw [h2]
      _ = x * y := by group
  rw [twoResidual_top_eq h]
  exact sup_le (key h) (key h.symm)

theorem exists_isComponent_of_isCyclic (h : IsGoldschmidtTriple G₁ G₂)
    (hO : CFSG.pPrimeCore 3 D = ⊥) (hcyc : IsCyclic ↥(Open.pCore 3 D)) :
    ∃ K : Subgroup D, CFSG.IsComponent K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  set P := Open.pCore 3 D with hPdef
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hP3 : IsPGroup 3 ↥P := CFSG.LieType.BorelTits.pCore_isPGroup 3
  have hlayer : CFSG.layer D = ⊥ := by
    rw [CFSG.layer, sSup_eq_bot]
    intro K hK
    exact absurd hK (hno K)
  have hF : CFSG.generalizedFitting D = P := by
    rw [CFSG.generalizedFitting, hlayer, sup_bot_eq, CFSG.Fitting_eq_pcore D 3 hO, hPdef]
  have hC := CFSG.centralizer_generalizedFitting_le D
  rw [hF] at hC
  have hLP : twoResidual (⊤ : Subgroup D) ≤ P :=
    (twoResidual_le_centralizer_of_isCyclic h hcyc).trans hC
  have hL₁ := card_twoResidual_eq_three_of_le h hP3 ((twoResidual_mono le_top).trans hLP)
  have hL₂ := card_twoResidual_eq_three_of_le h.symm hP3 ((twoResidual_mono le_top).trans hLP)
  have hL : twoResidual G₁ = twoResidual G₂ := by
    have h1 : twoResidual G₁ ≤ P := (twoResidual_mono le_top).trans hLP
    have h2 : twoResidual G₂ ≤ P := (twoResidual_mono le_top).trans hLP
    rcases A1c.le_total_of_isCyclic_isPGroup (C := P) hP3 h1 h2 with hle | hle
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hL₁, hL₂])
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hL₁, hL₂])).symm
  have hG : G₁ = G₂ := by
    calc G₁ = G₁ ⊓ G₂ ⊔ twoResidual G₁ := (inf_sup_twoResidual_left h).symm
      _ = G₁ ⊓ G₂ ⊔ twoResidual G₂ := by rw [hL]
      _ = G₂ := inf_sup_twoResidual_right h
  have hc := card_left h
  rw [hG, inf_idem] at hc
  have hpos : 0 < Nat.card ↥G₂ := Nat.card_pos
  omega

theorem le_twoResidual_of_isComponent {K : Subgroup D} (hK : CFSG.IsComponent K) :
    K ≤ twoResidual (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  have hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hperf : Group.IsPerfect ↥K := hK.1.1
  set N := L.subgroupOf K with hNdef
  have hQ2 : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup D) (x : D) (Subgroup.mem_top _)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have hsub : Subsingleton (↥K ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have : Group.IsNilpotent (↥K ⧸ N) := hQ2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (G := ↥K ⧸ N) inferInstance
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem twoResidual_eq_of_le (h : IsGoldschmidtTriple G₁ G₂) {K : Subgroup D}
    (hK : CFSG.IsComponent K) (h₁ : twoResidual G₁ ≤ K) (h₂ : twoResidual G₂ ≤ K) :
    twoResidual (⊤ : Subgroup D) = K := by
  refine le_antisymm ?_ (le_twoResidual_of_isComponent hK)
  rw [twoResidual_top_eq h]
  exact sup_le h₁ h₂

theorem generalizedFitting_eq_twoResidual (h : IsGoldschmidtTriple G₁ G₂)
    (hO : CFSG.pPrimeCore 3 D = ⊥) {K : Subgroup D} (hK : CFSG.IsComponent K)
    (h₁ : twoResidual G₁ ≤ K) (h₂ : twoResidual G₂ ≤ K) :
    CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLK := twoResidual_eq_of_le h hK h₁ h₂
  have hlayer : CFSG.layer D = K := by
    refine le_antisymm (sSup_le fun K' hK' => ?_) (le_sSup hK)
    have hK'L := le_twoResidual_of_isComponent hK'
    rw [hLK] at hK'L
    rcases CFSG.LocalCores.distinct_components_commute hK' hK with heq | hc
    · exact heq.le
    · exfalso
      have hperf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hK'.1.1
      have hbot : K' = ⊥ := by
        rw [← hperf, eq_bot_iff, ← hc]
        exact Subgroup.commutator_mono le_rfl hK'L
      have : Nontrivial ↥K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
      rw [hbot] at this
      exact not_nontrivial_iff_subsingleton.mpr inferInstance this
  have hP : CFSG.pCore 3 D ≤ twoResidual (⊤ : Subgroup D) := by
    intro x hx
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨x, hx⟩
    have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_twoResidual_of_odd (Subgroup.mem_top x)
      (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk'))
  rw [CFSG.generalizedFitting, hlayer, CFSG.Fitting_eq_pcore D 3 hO, ← hLK]
  exact sup_eq_right.mpr hP

@[expose] def ComponentConjugatesBound : Prop :=
  ∀ (D : Type) [Group D] [Finite D],
    (∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    ∀ K : Subgroup D, CFSG.IsComponent K → (Subgroup.normalizer (K : Set D)).index ≤ 2

@[expose] def F617NonquasisimpleCase : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    IsCyclic ↥(Open.pCore 3 D) → ∀ K : Subgroup D, CFSG.IsComponent K → K.Normal →
    twoResidual G₁ ≤ K → ¬ twoResidual G₂ ≤ K → K ⊔ G₂ = ⊤ → IsF618CaseThree G₁ G₂

@[expose] def F618QuasisimpleCase : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D) →
    CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D)) → F618Conclusion G₁ G₂

theorem theoremF618Cyclic_of (hB : ComponentConjugatesBound) (hNQ : F617NonquasisimpleCase)
    (hQS : F618QuasisimpleCase) : TheoremF618Cyclic := by
  intro D _ _ G₁ G₂ h hX hcyc
  obtain ⟨X, _, _, hsq, hK, ⟨e⟩⟩ := hX
  have hX' : ∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X) :=
    ⟨X, inferInstance, inferInstance, hsq, hK, ⟨e⟩⟩
  obtain ⟨hO, -⟩ := pPrimeCore_eq_bot_and_pRank_le (hsq 3 Nat.prime_three (by norm_num)) e
  obtain ⟨K, hKc⟩ := exists_isComponent_of_isCyclic h hO hcyc
  obtain ⟨hKn, hcases, -⟩ := f6_10 h hKc (hB D hX' K hKc)
  rcases hcases with ⟨h₁, hsup⟩ | ⟨h₂, hsup⟩
  · by_cases h₂ : twoResidual G₂ ≤ K
    · exact hQS D G₁ G₂ h hX' (generalizedFitting_eq_twoResidual h hO hKc h₁ h₂)
        (twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1)
    · exact Or.inl (Or.inr (Or.inr (Or.inl (hNQ D G₁ G₂ h hX' hcyc K hKc hKn h₁ h₂ hsup))))
  · by_cases h₁ : twoResidual G₁ ≤ K
    · exact hQS D G₁ G₂ h hX' (generalizedFitting_eq_twoResidual h hO hKc h₁ h₂)
        (twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (hNQ D G₂ G₁ h.symm hX' hcyc K hKc hKn h₂ h₁ hsup))))

theorem theoremF618_of (hB : ComponentConjugatesBound) (hNQ : F617NonquasisimpleCase)
    (hQS : F618QuasisimpleCase) : TheoremF618 :=
  theoremF618_of_cyclic (theoremF618Cyclic_of hB hNQ hQS)

end F6

end CFSG.Quasithin

module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofSylow
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofLine
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjRep
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.RankThree.PartOne.BRANCH.RankArith
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

theorem exists_tup_of_pow_three {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3)
    {l : Fin TwistTag.D4.tag.rank → Kˣ} (hl : ∀ i, l i ^ 3 = 1) : ∃ γ : Exp3, l = tup ω γ := by
  choose m hm hlm using fun i => eq_pow_of_pow_three hω (hl i)
  refine ⟨fun i => (m i : ZMod 3), funext fun i => ?_⟩
  simp only [tup]
  rw [ZMod.val_cast_of_lt (hm i)]
  exact hlm i

theorem exists_tup_of_rootDiagUnit_pow
    {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) {l : Fin TwistTag.D4.tag.rank → Kˣ}
    (hl : rootDiagUnit TwistTag.D4.tag l ^ 3 = 1) : ∃ γ : Exp3, l = tup ω γ := by
  have h1 : rootDiagUnit TwistTag.D4.tag (l ^ 3) = rootDiagUnit TwistTag.D4.tag 1 := by
    rw [rootDiagUnit_pow', hl, rootDiagUnit_one]
  have h2 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  exact exists_tup_of_pow_three hω fun i => congrFun h2 i

theorem tup_ne_one {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) {γ : Exp3} (hγ : γ ≠ 0) :
    tup ω γ ≠ 1 := by
  intro h
  apply hγ
  apply tup_injective hω
  rw [h]
  funext i
  simp [tup]

theorem hoElt_eq_tup_gA2 {K : Type} [Field K] {σ : K ≃+* K} {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hσω : Units.map σ.toRingHom.toMonoidHom ω = ω) :
    hoElt σ ω = rootDiagUnit TwistTag.D4.tag (tup ω gA2) := by
  rw [hoElt_eq_rootDiagUnit, hσω, hσω]
  congr 1
  funext j
  rw [← zpow_add, ← zpow_add, zpow_eq_pow_val hω3]
  simp only [tup]
  have e : ((TwistTag.D4.tag.cartan n0 j + TwistTag.D4.tag.cartan n1 j +
      TwistTag.D4.tag.cartan n3 j : ℤ) : ZMod 3) = gA2 j := by
    fin_cases j <;> decide
  rw [e]

theorem pow_mod_three_of_even {q : ℕ} (hq : q % 3 = 1 ∨ q % 3 = 2) (n : ℕ) :
    q ^ (2 * n) % 3 = 1 := by
  have h2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  rw [pow_mul, Nat.pow_mod, h2, one_pow]
  norm_num

theorem exists_conj_commute_tup_gA2 {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {z : ModGL TwistTag.D4.tag K} (hz : z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) :
    ∃ (ζ : Lˣ) (g : ModGL TwistTag.D4.tag L), orderOf ζ = 3 ∧
      g ∈ adjointGroup TwistTag.D4.tag L ∧
      g * baseChangeGL (algebraMap K L) z * g⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA2) =
        rootDiagUnit TwistTag.D4.tag (tup ζ gA2) * (g * baseChangeGL (algebraMap K L) z * g⁻¹) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓp : ℓ.Prime := hℓ.out
  set q := ℓ ^ f with hqdef
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have : ¬ 3 ∣ q := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
    omega
  have hcube : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  let K₂ := FiniteField.Extension K ℓ 2
  have : CharP K₂ ℓ := charP_of_injective_algebraMap (algebraMap K K₂).injective ℓ
  have hK₂ : Nat.card K₂ = (ℓ ^ (2 * f)) ^ 3 := by
    rw [FiniteField.natCard_extension, hK, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  have hcube₂ : ∀ c : K₂, c ^ ((ℓ ^ (2 * f)) ^ 3) = c := fun c => by
    have : Fintype K₂ := Fintype.ofFinite K₂
    rw [← hK₂, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set σ₂ : K₂ ≃+* K₂ := iterateFrobeniusEquiv K₂ ℓ (4 * f) with hσ₂def
  have hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ (2 * f)) ^ 2) := fun c => by
    rw [hσ₂def, iterateFrobeniusEquiv_def, ← pow_mul]
    ring_nf
  have hσ₂3 : σ₂ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_three_apply, hσ₂, hσ₂, hσ₂, ← pow_mul, ← pow_mul]
    have e : (ℓ ^ (2 * f)) ^ 2 * ((ℓ ^ (2 * f)) ^ 2 * (ℓ ^ (2 * f)) ^ 2) =
        (ℓ ^ (2 * f)) ^ 3 * (ℓ ^ (2 * f)) ^ 3 := by ring
    rw [e, pow_mul, hcube₂, hcube₂]
    rfl
  set ι := algebraMap K K₂ with hιdef
  have hcomm₂ : ι.comp σ.toRingHom = σ₂.toRingHom.comp ι := by
    refine RingHom.ext fun c => ?_
    change ι (σ c) = σ₂ (ι c)
    rw [hσ, hσ₂, ← map_pow]
    congr 1
    have e : (ℓ ^ (2 * f)) ^ 2 = q ^ 3 * q := by rw [hqdef]; ring
    rw [e, pow_mul, hcube]
  set Γ := graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom with hΓ
  have hQ2 : 2 ≤ ℓ ^ (2 * f) := Nat.one_lt_pow (by omega) hℓp.one_lt
  have hQ3 : ℓ ^ (2 * f) % 3 = 1 := by
    rw [mul_comm, pow_mul]
    rw [Nat.pow_mod]
    rcases hq3 with h | h <;> rw [← hqdef, h]
  obtain ⟨hC, hTor, -⟩ := triality_both_orientations_exact_finite_order ℓ (2 * f) hℓp (by omega)
    K₂ hK₂ 2 (Or.inr rfl) σ₂.toRingHom hσ₂
  let Ω := AlgebraicClosure K₂
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K₂ Ω).injective ℓ
  obtain ⟨-, -, hΓeq, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ
    (2 * f) hℓp (by omega) K₂ hK₂ Ω 2 (Or.inr rfl) σ₂.toRingHom hσ₂
    (iterateFrobenius Ω ℓ (2 * f)) (fun c => iterateFrobenius_def ℓ (2 * f) c)
  set T : Subgroup Γ := (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom).subgroupOf Γ with hT
  have hTtor : ∀ x ∈ T, (x : ModGL TwistTag.D4.tag K₂) ∈ torusGroup TwistTag.D4.tag K₂ ∧
      (x : ModGL TwistTag.D4.tag K₂) ∈ twistedFixedGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    intro x hx
    exact Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hTtor x hx).1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hl]
    exact rootDiagUnit_mul_comm_of_mem_torusGroup l (hTtor y hy).1
  have hle1 : graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ≤ Γ := graphFixedRootTorus_le _ _ _
  have hTcard : Nat.card T = ((ℓ ^ (2 * f)) ^ 3 - 1) * (ℓ ^ (2 * f) - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv]
    exact hTor
  have hidx : ¬ 9 ∣ T.index := by
    have hmul := T.index_mul_card
    rw [hTcard, hC] at hmul
    exact CFSG.RankThree.PartOne.BRANCH.not_nine_dvd_triality_split hQ2 hQ3
      (by rw [mul_comm]; exact hmul)
  obtain ⟨hzC, hzF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1
    (graphFixedRootGroup_le _ _ _ hz)
  have hz₂ : baseChangeGL ι z ∈ Γ := by
    rw [hΓ, ← hΓeq]
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι hzC, ?_⟩
    rw [twistHom_baseChangeGL ι hcomm₂, hzF]
  set z₂ : Γ := ⟨baseChangeGL ι z, hz₂⟩ with hz₂def
  have hz₂3 : z₂ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change baseChangeGL ι z ^ 3 = 1
    rw [← map_pow, hz3, map_one]
  obtain ⟨g, hg⟩ := exists_conj_normalizes_torsion3 T hTab hidx hz₂3
  have h3dvd : 3 ∣ Nat.card K₂ˣ := by
    rw [Nat.card_units, hK₂, ← pow_mul]
    have h1 := pow_mod_three_of_even (q := ℓ) (by
      rcases Nat.lt_or_ge (ℓ % 3) 1 with h | h
      · exfalso
        apply hℓ3
        have h0 : ℓ % 3 = 0 := by omega
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
      · omega) (f * 3)
    rw [show 2 * f * 3 = 2 * (f * 3) by ring]
    have h2 : 1 ≤ ℓ ^ (2 * (f * 3)) := Nat.one_le_pow _ _ hℓp.pos
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := K₂ˣ) 3 h3dvd
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hσ₂ω : Units.map σ₂.toRingHom.toMonoidHom ω = ω := by
    have h1 : Units.map σ₂.toRingHom.toMonoidHom ω = ω ^ (ℓ ^ (4 * f)) := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      rfl)
    rw [h1, pow_eq_pow_mod _ hω3]
    have h4 : ℓ ^ (4 * f) % 3 = 1 := by
      rw [show 4 * f = 2 * (2 * f) by ring]
      rcases Nat.lt_or_ge (ℓ % 3) 1 with h | h
      · exfalso
        apply hℓ3
        have h0 : ℓ % 3 = 0 := by omega
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
      · exact pow_mod_three_of_even (by omega) _
    rw [h4, pow_one]
  have ha₀eq := hoElt_eq_tup_gA2 (σ := σ₂) hω3 hσ₂ω
  have ha₀Γ : rootDiagUnit TwistTag.D4.tag (tup ω gA2) ∈ Γ := by
    rw [← ha₀eq]
    exact hoElt_mem hσ₂3 ω
  have ha₀tor : rootDiagUnit TwistTag.D4.tag (tup ω gA2) ∈ torusGroup TwistTag.D4.tag K₂ := by
    rw [← ha₀eq]
    exact hoElt_mem_torusGroup σ₂ ω
  set a₀ : Γ := ⟨rootDiagUnit TwistTag.D4.tag (tup ω gA2), ha₀Γ⟩ with ha₀def
  have ha₀T : a₀ ∈ T := Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨ha₀tor, graphFixedRootGroup_le _ _ _ ha₀Γ⟩, ha₀Γ⟩)
  have ha₀3 : a₀ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change rootDiagUnit TwistTag.D4.tag (tup ω gA2) ^ 3 = 1
    rw [← rootDiagUnit_pow', tup_pow_three hω3, rootDiagUnit_one]
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    have h1 : rootDiagUnit TwistTag.D4.tag (tup ω gA2) = rootDiagUnit TwistTag.D4.tag 1 := by
      rw [rootDiagUnit_one]
      exact congrArg Subtype.val h
    exact tup_ne_one hω (by decide) (CFSG.LieType.Chevalley.rootDiagUnit_injective h1)
  set y₁ := g⁻¹ * z₂ * g with hy₁
  have hφ := hg a₀ ⟨ha₀T, ha₀3⟩
  obtain ⟨hφtor, hφfix⟩ := hTtor _ hφ.1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hφtor
  have hl3 : rootDiagUnit TwistTag.D4.tag l ^ 3 = 1 := by
    rw [← hl, ← Subgroup.coe_pow, hφ.2, Subgroup.coe_one]
  obtain ⟨γ, rfl⟩ := exists_tup_of_rootDiagUnit_pow hω hl3
  have hγ : rhoExp γ = γ := by
    refine rhoExp_eq_of_twistHom_fixed (σ := σ₂.toRingHom) hω hσ₂ω ?_
    rw [← hl]
    exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hφfix).2
  have hy₁C : (y₁ : ModGL TwistTag.D4.tag K₂) ∈ adjointGroup TwistTag.D4.tag K₂ :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ y₁.2)).1
  have hconj : (y₁ : ModGL TwistTag.D4.tag K₂) * rootDiagUnit TwistTag.D4.tag (tup ω gA2) *
      (y₁ : ModGL TwistTag.D4.tag K₂)⁻¹ = rootDiagUnit TwistTag.D4.tag (tup ω γ) := by
    rw [← hl]
    rfl
  have hcase := eq_of_conj_gA2 hω hγ hy₁C ha₀tor (hl ▸ hφtor) hconj
  have hcases : y₁ * a₀ * y₁⁻¹ = a₀ ∨ y₁ * a₀ * y₁⁻¹ = a₀ ^ 2 := by
    rcases hcase with h | h
    · left
      apply Subtype.ext
      change (y₁ : ModGL TwistTag.D4.tag K₂) * rootDiagUnit TwistTag.D4.tag (tup ω gA2) *
        (y₁ : ModGL TwistTag.D4.tag K₂)⁻¹ = rootDiagUnit TwistTag.D4.tag (tup ω gA2)
      rw [hconj, h]
    · right
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      change (y₁ : ModGL TwistTag.D4.tag K₂) * rootDiagUnit TwistTag.D4.tag (tup ω gA2) *
        (y₁ : ModGL TwistTag.D4.tag K₂)⁻¹ = rootDiagUnit TwistTag.D4.tag (tup ω gA2) ^ 2
      rw [hconj, h, tup_two_mul hω3, rootDiagUnit_pow']
  have hy₁3 : y₁ ^ 3 = 1 := by
    rw [hy₁, show g⁻¹ * z₂ * g = g⁻¹ * z₂ * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hz₂3]
    group
  have hcommΓ := commute_of_conj_eq_or_sq hy₁3 ha₀3 ha₀1 hcases
  let j : K₂ →ₐ[K] L := IsAlgClosed.lift
  set jr : K₂ →+* L := (j : K₂ →+* L) with hjr
  have hjι : jr.comp ι = algebraMap K L := j.comp_algebraMap
  set ζ : Lˣ := Units.map jr.toMonoidHom ω with hζdef
  have hζ : orderOf ζ = 3 := by
    rw [hζdef, orderOf_injective _ (Units.map_injective jr.injective) ω, hω]
  have hjd : baseChangeGL jr (rootDiagUnit TwistTag.D4.tag (tup ω gA2)) =
      rootDiagUnit TwistTag.D4.tag (tup ζ gA2) := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    simp only [tup, map_pow, hζdef]
  have hgC : (g : ModGL TwistTag.D4.tag K₂) ∈ adjointGroup TwistTag.D4.tag K₂ :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ g.2)).1
  refine ⟨ζ, (baseChangeGL jr (g : ModGL TwistTag.D4.tag K₂))⁻¹, hζ,
    inv_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup jr hgC), ?_⟩
  have hzL : baseChangeGL (algebraMap K L) z = baseChangeGL jr (baseChangeGL ι z) := by
    rw [baseChangeGL_baseChangeGL, hjι]
  have key : (baseChangeGL jr (g : ModGL TwistTag.D4.tag K₂))⁻¹ *
      baseChangeGL (algebraMap K L) z * (baseChangeGL jr (g : ModGL TwistTag.D4.tag K₂))⁻¹⁻¹ =
        baseChangeGL jr (y₁ : ModGL TwistTag.D4.tag K₂) := by
    rw [hzL, inv_inv, hy₁, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_mul, map_inv]
  rw [key, ← hjd, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val hcommΓ

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

module

public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedE6OddDatum
public import CFSG.LieType.Chevalley.CLSOddDiagramFourGroup
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Layer

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Balance.Bootstrap

theorem e6odd_exists_orbit :
    ∃ (a : Fin TwistTag.E6.foldedTag.rank) (k₁ : Fin TwistTag.E6.tag.rank),
      2 ≤ (TwistTag.E6.orbit a).card ∧
      ((TwistTag.E6.orbitWord a).map fun i => TwistTag.E6.tag.cartan i k₁).sum % 2 = 1 :=
  ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, by decide⟩

theorem e6odd_HSL_neg_one_mem_center {L : Type*} [Field L] :
    HSL (-1 : Lˣ) ∈ Subgroup.center (SL2 L) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem e6odd_HSL_neg_one_sq {L : Type*} [Field L] : HSL (-1 : Lˣ) ^ 2 = 1 := by
  rw [pow_two]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two]

section Rank

theorem exists_involution_perfect_centralizer (t : TwistTag)
    (hrows : ∃ (a : Fin t.foldedTag.rank) (k₁ : Fin t.tag.rank), 2 ≤ (t.orbit a).card ∧
      ((t.orbitWord a).map fun i => t.tag.cartan i k₁).sum % 2 = 1)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ∃ (s : ↥(graphFixedRootGroup t K σ.toRingHom))
      (P : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)),
      s ≠ 1 ∧ s ^ 2 = 1 ∧ P ≤ Subgroup.centralizer {s} ∧ Group.IsPerfect ↥P ∧ P ≠ ⊥ := by
  classical
  obtain ⟨a, k₁, ha2, hsign⟩ := hrows
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = p ^ (f * t.order) := by rw [hK, ← pow_mul]
  have hcharK : CharP K p :=
    finite_field_prime_power_characteristic hp (Nat.mul_pos (by omega) t.order_pos) hK2
  have hringchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ' : σ'.toRingHom = σ.toRingHom := RingHom.ext fun c => (hσ' c).trans (hσ c).symm
  have hLcard : Nat.card (orbitField t K σ.toRingHom a) =
      (p ^ f) ^ (t.orbit a).card := by
    rw [← hσσ']
    exact hcard a
  have hq3 : 3 ≤ p ^ f := by
    have h1 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact h1.trans (Nat.le_self_pow (by omega) p)
  have hL9 : 9 ≤ Nat.card (orbitField t K σ.toRingHom a) := by
    rw [hLcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
      _ ≤ (p ^ f) ^ (t.orbit a).card := Nat.pow_le_pow_right (by omega) ha2
  have hperfSL : Group.IsPerfect (SL2 (orbitField t K σ.toRingHom a)) := by
    haveI : Fintype (orbitField t K σ.toRingHom a) := Fintype.ofFinite _
    have h4 : 4 ≤ (Finset.univ : Finset (orbitField t K σ.toRingHom a)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  obtain ⟨R, -, -, hRH, -, -, hRrange, hRle, -, -⟩ :=
    exceptional_fixed_rank_one_central_image t K σ.toRingHom a
  have hmem : ∀ g, R g ∈ graphFixedRootGroup t K σ.toRingHom := fun g =>
    hRle (hRrange ▸ ⟨g, rfl⟩)
  let R₁ : SL2 (orbitField t K σ.toRingHom a) →*
      ↥(graphFixedRootGroup t K σ.toRingHom) := R.codRestrict _ hmem
  have hR₁ : ∀ g, ((R₁ g : ↥(graphFixedRootGroup t K σ.toRingHom)) :
      ModGL t.tag K) = R g := fun g => rfl
  have hs1 : R₁ (HSL (-1)) ≠ 1 := by
    intro h
    have h1 := congrArg (fun x : ↥(graphFixedRootGroup t K σ.toRingHom) =>
      (x : ModGL t.tag K)) h
    simp only [hR₁, hRH, Subgroup.coe_one] at h1
    rw [coe_orbitH_neg_one, list_prod_torusElt_neg_one] at h1
    rw [← rootDiagUnit_one] at h1
    refine units_neg_one_ne_one hringchar ?_
    rw [← torusWordSigns_of_odd hsign, ← Pi.one_apply (M := fun _ => Kˣ) k₁]
    exact congrFun (rootDiagUnit_injective h1) k₁
  refine ⟨R₁ (HSL (-1)), R₁.range, hs1, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, e6odd_HSL_neg_one_sq, map_one]
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.1 e6odd_HSL_neg_one_mem_center g]
  · rw [Subgroup.isPerfect_iff, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    have := hperfSL.commutator_eq_top
    rw [commutator] at this
    rw [this]
  · intro h
    apply hs1
    have : R₁ (HSL (-1)) ∈ R₁.range := ⟨_, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this

end Rank

section Core

theorem hasInvolutionComponent_of_perfect_centralizer_E6
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (P : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) (hPs : P ≤ Subgroup.centralizer {s})
    (hPperf : Group.IsPerfect ↥P) (hP1 : P ≠ ⊥) :
    CFSG.Open.HasInvolutionComponent ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
  have hKo : Nat.card K = (p ^ f) ^ TwistTag.E6.order := hK
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK2 : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK2
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd K hKo σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) =
        twistedFixedGroup TwistTag.E6 k Fr := rfl
  let Φ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hΦinj : Function.Injective Φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hΦR : ∀ z, Φ z ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) := fun z => by
    rw [hRF]
    exact hHR ⟨z, z.2, rfl⟩
  have hΦrange : Φ.range = ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))⁆ := by
    rw [hRF, hder, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΦker : Φ.ker ≤ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ).2 hΦinj]
    exact bot_le
  have hy2 : Φ s ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  obtain ⟨-, -, D, w, -, hw, -, -, -, -, -, -, hcent⟩ :=
    e6_exists_datum_conj_centralizer p hp2 halg hf (hΦR s) hy2
  obtain ⟨ψ, hker, hXs, hH, hPr⟩ := exists_cover_of_conj_centralizer Φ hΦker
    (adjointGroup TwistTag.E6.tag k) _ inf_le_left hΦR hΦrange w hw s _ hcent
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψinj : Function.Injective ψ := by
    refine (MonoidHom.ker_eq_bot_iff ψ).1 ?_
    rw [eq_bot_iff, ← hZ]
    exact hker
  have hP'X : P.map ψ ≤ D.totalFixedGroup := by
    rintro _ ⟨z, hz, rfl⟩
    exact hH z (hPs hz)
  have hP'perf : Group.IsPerfect ↥(P.map ψ) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hPperf]
  have hP'1 : P.map ψ ≠ ⊥ := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP1
    intro h
    have : ψ z ∈ P.map ψ := Subgroup.mem_map_of_mem ψ hz
    rw [h, Subgroup.mem_bot] at this
    exact hz1 (Subtype.ext (hψinj (by rw [this]; exact (map_one ψ).symm)))
  obtain ⟨J', hJ'⟩ := exists_isQuasisimple_orbitGroupC_of_isPerfect D hP'X hP'perf hP'1
  have hsn := isSubnormal_orbitGroupC_totalFixedGroup D J'
  have hTr : (D.withOrbit J').orbitGroupC ≤ ψ.range :=
    hPr _ (le_of_isSubnormal_open hsn) (commutator_eq_of_isQuasisimple hJ')
  exact ⟨s, _, hs1, hs2, isComponentOf_commutator_comap ψ hker s hXs hH hsn hTr hJ'⟩

end Core

end CFSG.LocalAnalysis.UniqueFourCatalog

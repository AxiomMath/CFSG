module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.RankThree.PartOne.KC.SymplecticSubfield

public section

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  centralizer_commutator_sympFour not_isMulCommutative_commutator_sympFour)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem symplectic_prime_numerics {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 2 ≤ r)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card (StatedProj (StatedSp r K))) :
    ∃ ℓ f' : ℕ, ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ f' ∧ Nat.card K = ℓ ^ f' ∧ p ≠ ℓ ∧ 3 < p := by
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK⟩ := exists_char_card K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hSL := SymplecticFlag.card_statedSp (K := K) r
  have hsplit := (spScalars r K).card_eq_card_quotient_mul_card_subgroup
  have hZ := SymplecticFlag.card_scalars_dvd (K := K) (r := r) (by omega)
  have hZ2 : Nat.card (spScalars r K) = Nat.gcd 2 (Nat.card K - 1) :=
    card_spScalars_eq_gcd K (by omega)
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    apply hpT
    have hSLp : p ∣ Nat.card (StatedSp r K) := by
      rw [hSL, hK]
      exact Dvd.dvd.mul_right (dvd_pow (dvd_pow_self p (by omega)) (by positivity)) _
    have hcop : Nat.Coprime p (Nat.card (spScalars r K)) := by
      have hpq : p ∣ Nat.card K := by
        rw [hK]
        exact dvd_pow_self p (by omega)
      have h1 : Nat.Coprime p (Nat.card K - 1) := by
        refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
        have : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hpq hd
        rw [Nat.sub_sub_self hq1.le] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      exact Nat.Coprime.coprime_dvd_right hZ h1
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop (hsplit ▸ hSLp)
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    have h3 : p ≠ 3 := by
      rintro rfl
      apply hpT
      have h3SL : 3 ∣ Nat.card (StatedSp r K) := by
        rw [hSL]
        by_cases h3q : 3 ∣ Nat.card K
        · exact Dvd.dvd.mul_right (dvd_pow h3q (by positivity)) _
        · refine Dvd.dvd.mul_left ?_ _
          have h2' : 3 ∣ Nat.card K ^ (2 * 1) - 1 := by
            have h0 : 0 < Nat.card K := by omega
            have : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
            have h' : Nat.card K ^ (2 * 1) % 3 = 1 := by
              rcases this with h | h <;> simp [Nat.pow_mod, h]
            have : 1 ≤ Nat.card K ^ (2 * 1) := Nat.one_le_pow _ _ h0
            omega
          exact h2'.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1)
            (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩))
      have hcop : Nat.Coprime 3 (Nat.card (spScalars r K)) := by
        rw [hZ2]
        exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop (hsplit ▸ h3SL)
    obtain ⟨m, hm⟩ := hodd
    omega
  exact ⟨ℓ, f', hℓ, hcharK, hf'1, hK, hpℓ, hp3⟩

theorem fieldClauses_projSp {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 2 ≤ r) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card (StatedProj (StatedSp r K)))
    (hNL : ∀ σ : K ≃+* K, orderOf σ = p →
      FStarSimple (signalizerFixedSubgroup (fieldAut r K σ)) →
      NonLocalized (signalizerFixedSubgroup (fieldAut r K σ))) :
    FieldClauses p (StatedProj (StatedSp r K)) := by
  rintro ⟨f, hf⟩
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK, hpℓ, hp3⟩ := symplectic_prime_numerics hr hp hodd hpT
  have hO := spOuter hℓ hf'1 hr hK
  have hfE : f ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd (by rw [hf]; exact hodd)
  have hfD : f ∉ spLinearAutGroup r K := by
    intro hfD
    have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp r K))
    have hfH : f ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K)) :=
      mem_of_pow_eq_one_of_relIndex_dvd_two (hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp
        (by omega) hfD (by rw [← hf]; exact pow_orderOf_eq_one f)
    have hdvd := orderOf_dvd_natCard
      (⟨f, hfH⟩ : CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K)))
    rw [Subgroup.orderOf_mk, hf] at hdvd
    exact hpT (hdvd.trans (Subgroup.card_range_dvd _))
  obtain ⟨-, σ, hσ, -⟩ := hO.descent p hp f hfE hfD hf
  have : NeZero r := ⟨by omega⟩
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hord : orderOf (fieldAut r K σ) = p := by
    rw [orderOf_injective (fieldAut r K) hO.fieldAut_injective σ]; exact hσ
  have hclause := CFSG.RankThree.PartOne.symplectic_prime_subfield_clause ℓ f' r p K hℓ hp hp3 hpℓ
    hf'1 hr hK σ hσ
  have hrange : (subfieldInj (r := r) σ).range = signalizerFixedSubgroup (fieldAut r K σ) := by
    rw [range_subfieldInj]
    exact (spFixedGroup_fieldAut_eq_range hodd hσp).symm
  let e : StatedProj (StatedSp r (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ))
      ≃* signalizerFixedSubgroup (fieldAut r K σ) :=
    (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ)).trans
      (MulEquiv.subgroupCongr hrange)
  have hF : FStarSimple (signalizerFixedSubgroup (fieldAut r K σ)) := by
    by_cases hex : r = 2 ∧ Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.descentField
        σ) = 2
    · obtain ⟨rfl, hk2⟩ := hex
      let e' := (e.symm.trans (statedProjEquivSympFour hk2))
      have hN : ∃ a b : commutator sympFour,
          a * b ≠ b * a := by
        have := not_isMulCommutative_commutator_sympFour
        rw [isMulCommutative_iff] at this
        push Not at this
        exact this
      have := isSimpleGroup_commutator_sympFour
      have h1 := isFStarSimple_of_simple_normal
        (commutator sympFour) hN
        centralizer_commutator_sympFour
      exact (fStarSimple_iff_isFStarSimple _).mpr
        ((McBride.Nonsolv.L514.isFStarSimple_congr e').mpr h1)
    · obtain ⟨hs, hperf⟩ := simple_perfect_statedProj
        (k := CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) hr hex
      have hsC : IsSimpleGroup (signalizerFixedSubgroup (fieldAut r K σ)) := e.symm.isSimpleGroup
      have hnC : ∃ a b : signalizerFixedSubgroup (fieldAut r K σ), a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        have hcomm : ∀ a b : StatedProj (StatedSp r
            (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)), a * b = b * a :=
          fun a b => e.injective (by rw [map_mul, map_mul]; exact hcon _ _)
        have : Nontrivial (StatedProj (StatedSp r
            (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ))) := hs.toNontrivial
        have : Group.IsSolvable (StatedProj (StatedSp r
            (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ))) :=
          Group.isSolvable_of_comm hcomm
        exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect this
      exact fStarSimple_of_simple hsC hnC
  refine ⟨fieldAut r K σ, hord, fixedClauses_of_stabilizer hord hF (hNL σ hσ) ?_⟩
  intro g hg
  rw [← hclause.2]
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have hc' : c ∈ signalizerFixedSubgroup (fieldAut r K σ) := hc
  have h1 := mulAut_conj_apply_conj g c
  rw [hg c hc'] at h1
  show MulAut.conj c * g = g * MulAut.conj c
  calc MulAut.conj c * g = (g * MulAut.conj c * g⁻¹) * g := by rw [h1]
    _ = g * MulAut.conj c := by group

theorem fieldClauses_statedPSp {T : Type} [Group T] {n ℓ f p : ℕ}
    (hm : StatedClassicalModel T .PSp n ℓ f) (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedPSp) : FieldClauses p T := by
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, -, ⟨eT⟩⟩ := hm
  have hpT' : ¬ p ∣ Nat.card (StatedProj (StatedSp n K)) := by
    rwa [← Nat.card_congr eT.toEquiv]
  exact FieldClauses.of_mulEquiv eT.symm
    (fieldClauses_projSp hn hp hodd hpT' (hNL K n hn p hp hodd hpT'))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
